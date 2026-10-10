import Mathlib
import OAI.Geometry.WeakMTW.Support.CompactLimitInjectivity

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology
namespace CompactContinuation
variable {P X Y : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]

 def CollisionExclusionAt (F : P × X → Y) (t : P) : Prop :=
  ∀ x : X, ∀ r : ℕ → P, ∀ p q : ℕ → X,
    Tendsto r atTop (𝓝 t) → Tendsto p atTop (𝓝 x) → Tendsto q atTop (𝓝 x) →
    (∀ j, p j ≠ q j) → (∀ j, F (r j,p j) = F (r j,q j)) → False

 omit [FirstCountableTopology P] [CompactSpace X] [T2Space X] [TopologicalSpace Y]
   [T2Space Y] in
 theorem local_injective_of_exclusion {F : P × X → Y} {t : P}
    (hexc : CollisionExclusionAt F t) (x : X) :
    ∃ N ∈ 𝓝 x, InjOn (fun p => F (t,p)) N := by
  classical
  by_contra hfail
  push Not at hfail
  let C : Set (X × X) := {z | z.1 ≠ z.2 ∧ F (t,z.1) = F (t,z.2)}
  have hcl : (x,x) ∈ closure C := by
    apply mem_closure_iff_nhds.mpr
    intro N hN
    obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hN
    have hn := hfail (U ∩ V) (inter_mem hU hV)
    change ¬(∀ ⦃a⦄, a ∈ U ∩ V → ∀ ⦃b⦄, b ∈ U ∩ V → F (t,a) = F (t,b) → a = b) at hn
    push Not at hn
    obtain ⟨a,ha,b,hb,hab,hne⟩ := hn
    exact ⟨(a,b),hUV ⟨ha.1,hb.2⟩,hne,hab⟩
  obtain ⟨z,hz,hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  exact hexc x (fun _ => t) (fun j => (z j).1) (fun j => (z j).2)
    tendsto_const_nhds (continuous_fst.continuousAt.tendsto.comp hlim)
    (continuous_snd.continuousAt.tendsto.comp hlim) (fun j => (hz j).1) (fun j => (hz j).2)

 omit [T2Space X] in
 theorem injectivity_nhds_of_exclusion {F : P × X → Y} (hF : Continuous F) {t : P}
    (hinj : Function.Injective (fun x => F (t,x)))
    (hexc : CollisionExclusionAt F t) :
    {r : P | Function.Injective (fun x => F (r,x))} ∈ 𝓝 t := by
  classical
  let G : Set P := {r | Function.Injective (fun x => F (r,x))}
  by_contra hfail
  have hcl : t ∈ closure Gᶜ := by
    rw [closure_compl,mem_compl_iff,mem_interior_iff_mem_nhds]
    exact hfail
  obtain ⟨r,hr,hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hbad (j : ℕ) : ∃ p q : X, p ≠ q ∧ F (r j,p) = F (r j,q) := by
    have hn : ¬Function.Injective (fun x => F (r j,x)) := hr j
    simp only [Function.Injective] at hn
    push Not at hn
    obtain ⟨p,q,he,hne⟩ := hn
    exact ⟨p,q,hne,he⟩
  choose p q hpq heq using hbad
  obtain ⟨⟨x,z⟩,_,ρ,hρ,hpqLim⟩ := (isCompact_univ : IsCompact (univ : Set (X × X))).tendsto_subseq
    (fun j => mem_univ (p j,q j))
  have hpLim : Tendsto (p ∘ ρ) atTop (𝓝 x) := continuous_fst.continuousAt.tendsto.comp hpqLim
  have hqLim : Tendsto (q ∘ ρ) atTop (𝓝 z) := continuous_snd.continuousAt.tendsto.comp hpqLim
  have hrLim := hlim.comp hρ.tendsto_atTop
  have hfP := hF.continuousAt.tendsto.comp (hrLim.prodMk_nhds hpLim)
  have hfQ := hF.continuousAt.tendsto.comp (hrLim.prodMk_nhds hqLim)
  have hxz : x = z := hinj (tendsto_nhds_unique hfP
    (hfQ.congr' (Filter.Eventually.of_forall (fun j => (heq (ρ j)).symm))))
  rw [← hxz] at hqLim
  exact hexc x (r ∘ ρ) (p ∘ ρ) (q ∘ ρ) hrLim hpLim hqLim
    (fun j => hpq (ρ j)) (fun j => heq (ρ j))

 theorem global_bijective [LocallyConnectedSpace Y] [PreconnectedSpace P]
    {F : P × X → Y} (hF : Continuous F)
    (hsurj : ∀ t, Function.Surjective (fun x => F (t,x)))
    (hexc : ∀ t, CollisionExclusionAt F t)
    (hstart : ∃ t, Function.Injective (fun x => F (t,x))) :
    ∀ t, Function.Bijective (fun x => F (t,x)) := by
  let G : Set P := {t | Function.Injective (fun x => F (t,x))}
  have hGo : IsOpen G := isOpen_iff_mem_nhds.mpr (fun t ht => injectivity_nhds_of_exclusion hF ht (hexc t))
  have hGc : IsClosed G := by
    apply IsSeqClosed.isClosed
    intro r t hr ht
    exact limit_injective hF ht (fun j => ⟨hr j,hsurj (r j)⟩)
      (local_injective_of_exclusion (hexc t))
  have hG : G = univ := (show IsClopen G from ⟨hGc,hGo⟩).eq_univ hstart
  intro t
  exact ⟨show t ∈ G from hG.symm ▸ mem_univ t,hsurj t⟩

end CompactContinuation
end

end WeakMTWGlobalSupport

end OAI
