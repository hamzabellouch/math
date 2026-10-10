import Mathlib
import OAI.Geometry.WeakMTW.Support.CriticalCollision
import OAI.Geometry.WeakMTW.Support.CompactHomotopyContinuation
import OAI.Geometry.WeakMTW.Support.CriticalNonconjugacy

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [Nonempty ι]

 abbrev ActivePoint (y : ι → M) (h : ι → ℝ) := ↥(activeHullGraph (n := n) y h)

 def activeProjection (y : ι → M) (h : ι → ℝ) (s : ℝ) (p : ActivePoint (n := n) y h) : M :=
   exp p.val.1 (s•p.val.2)

 theorem activeProjection_continuous (y : ι → M) (h : ι → ℝ) :
     Continuous (fun q : ℝ × ActivePoint (n := n) y h => activeProjection y h q.1 q.2) :=
   scaledExp_continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

 theorem tendsto_ite_same {X : Type*} [TopologicalSpace X] {p q : ℕ → X} {x : X}
     (hp : Tendsto p atTop (𝓝 x)) (hq : Tendsto q atTop (𝓝 x)) (C : ℕ → Prop)
     [DecidablePred C] : Tendsto (fun j => if C j then p j else q j) atTop (𝓝 x) := by
   intro U hU
   change ∀ᶠ j in atTop, (if C j then p j else q j) ∈ U
   filter_upwards [hp hU,hq hU] with j hpj hqj
   split_ifs <;> assumption

 theorem active_collision_same_limit_false (y : ι → M) (h : ι → ℝ)
     (hMTW : HasWeakMTW (n := n) (M := M))
     {p q : ℕ → ActivePoint (n := n) y h} {p₀ : ActivePoint (n := n) y h}
     (hp : Tendsto p atTop (𝓝 p₀)) (hq : Tendsto q atTop (𝓝 p₀))
     {sⱼ : ℕ → ℝ} {s : ℝ} (hs : Tendsto sⱼ atTop (𝓝 s))
     (hpos : ∀ j, 0 < sⱼ j) (hs0 : 0 ≤ s) (hs1 : s < 1)
     (hne : ∀ j, p j ≠ q j)
     (hcollision : ∀ j, activeProjection y h (sⱼ j) (p j) = activeProjection y h (sⱼ j) (q j))
     (hbelow : ∀ r, 0 ≤ r → r < s → ∀ a ∈ activeHull (n := n) y h p₀.val.1, r•a ∈ injectivityDomain p₀.val.1)
     (hn : Nonconjugate p₀.val.1 (s•p₀.val.2)) : False := by
   classical
   let C : ℕ → Prop := fun j => scaledPoleValue y h (sⱼ j) (q j).val ≤ scaledPoleValue y h (sⱼ j) (p j).val
   let p' : ℕ → ActivePoint (n := n) y h := fun j => if C j then p j else q j
   let q' : ℕ → ActivePoint (n := n) y h := fun j => if C j then q j else p j
   have hp' := tendsto_ite_same hp hq C
   have hq' := tendsto_ite_same hq hp C
   have hpv : Tendsto (fun j => (p' j).val) atTop (𝓝 p₀.val) := continuous_subtype_val.continuousAt.tendsto.comp hp'
   have hqv : Tendsto (fun j => (q' j).val) atTop (𝓝 p₀.val) := continuous_subtype_val.continuousAt.tendsto.comp hq'
   have hqb : Tendsto (fun j => (q' j).val.1) atTop (𝓝 p₀.val.1) :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.continuousAt.tendsto.comp hqv
   apply critical_collision_sequence_false y h hMTW hpv hqb hs
     (tangentScale_continuous.continuousAt.tendsto.comp (hs.prodMk_nhds hqv))
     (Eventually.of_forall hpos) hs0 hs1 (fun j => (p' j).property) _ _ _ hbelow hn
   · apply Eventually.of_forall
     intro j he
     have he' : p' j = q' j := Subtype.ext he
     dsimp [p',q'] at he'
     split_ifs at he' with _hj
     · exact hne j he'
     · exact hne j he'.symm
   · apply Eventually.of_forall
     intro j
     change activeProjection y h (sⱼ j) (p' j) = activeProjection y h (sⱼ j) (q' j)
     by_cases hj : C j
     · simpa only [p',q',ite_eq_left hj] using hcollision j
     · simpa only [p',q',ite_eq_right hj] using (hcollision j).symm
   · apply Eventually.of_forall
     intro j
     dsimp [p',q']
     split_ifs with hj
     · exact hj
     · exact (not_le.mp hj).le

 theorem active_collision_exclusion (y : ι → M) (h : ι → ℝ)
     (hMTW : HasWeakMTW (n := n) (M := M)) {s : ℝ} (_hs : 0 < s) (hs1 : s < 1)
     (hbelow : ∀ r, 0 ≤ r → r < s → ∀ p ∈ activeHullGraph (n := n) y h,
       r•p.2 ∈ injectivityDomain p.1)
     (hmin : ∀ p ∈ activeHullGraph (n := n) y h, s•p.2 ∈ minimizingDomain p.1)
     (t : Ioc (0 : ℝ) s) :
     CompactContinuation.CollisionExclusionAt
       (fun q : Ioc (0 : ℝ) s × ActivePoint (n := n) y h => activeProjection y h q.1.val q.2) t := by
   intro p₀ r p q hr hp hq hne hcol
   have htv : 0 < t.val := t.property.1
   have hts : t.val ≤ s := t.property.2
   have hmin_t : ∀ x a, a ∈ activeHull (n := n) y h x → t.val•a ∈ minimizingDomain x := by
     intro x a ha
     obtain ht | ht := lt_or_eq_of_le hts
     · exact injectivity_subset_minimizing x (hbelow t.val htv.le ht ⟨x,a⟩ ha)
     · rw [ht]
       exact hmin ⟨x,a⟩ ha
   have hn := activeHull_critical_nonconjugate hMTW y h htv.le (hts.trans_lt hs1)
     hmin_t p₀.val.1 (b := p₀.val.2) p₀.property
   exact active_collision_same_limit_false y h hMTW hp hq
     (continuous_subtype_val.continuousAt.tendsto.comp hr) (fun j => (r j).property.1)
     htv.le (hts.trans_lt hs1) hne hcol
     (fun u hu hut a ha => hbelow u hu (hut.trans_le hts) ⟨p₀.val.1,a⟩ ha) hn

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
