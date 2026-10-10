import Mathlib
import OAI.MeasureTheory.Falconer.Estimates.ActualFarBuffer
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.DirectPolicyWitness
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Fourier.StationaryInverseUnit3
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphCapScaleInvCrude
import OAI.MeasureTheory.FalconerCompletion.Graphs.LiteralDyadicPaths
import OAI.MeasureTheory.FalconerCompletion.Recursion.MaskScale2
import OAI.MeasureTheory.FalconerCompletion.Recursion.TreeCellMembershipConstantOnFinerGrid

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Classical
variable {n : ℕ}

structure RecursiveEnvironmentND (n : ℕ) where
  ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))
  mass : ℝ → ℝ
  N : ℕ
  q : ℕ
  J : ℕ
  sig : ℝ
  C : ℝ

namespace RecursiveEnvironmentND
noncomputable def profile (e : RecursiveEnvironmentND n) : ℕ → ℝ :=
  adjustedProfile (d:=n+1) e.mass e.N

def distanceData (e : RecursiveEnvironmentND n) (a t i : ℕ) (X Y : CellPath (n+1)) :
    PositiveDistanceState (n+1) :=
  ⟨e.ρ,e.mass,e.N,e.q,a,t,e.J,i,e.sig,e.C,X,Y⟩
end RecursiveEnvironmentND

structure RecursiveAngularND (n : ℕ) extends RecursiveEnvironmentND n where
  a₀ : ℕ
  t₀ : ℕ
  a : ℕ
  v : ℕ
  i : ℕ
  X : CellPath (n+1)
  Y : CellPath (n+1)

namespace RecursiveAngularND
noncomputable def profile (e : RecursiveAngularND n) : ℕ → ℝ := e.toRecursiveEnvironmentND.profile
noncomputable def fullList (e : RecursiveAngularND n) : Finset PolicyDescriptor :=
  policyDescriptorList e.profile e.N e.q e.a₀ e.t₀
noncomputable def retainedList (e : RecursiveAngularND n) (r : ℕ) : Finset PolicyDescriptor :=
  unreachedDescriptorList e.profile e.N e.q e.a₀ e.t₀ r
noncomputable def symbol (e : RecursiveAngularND n)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (r : ℕ) :
    EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) → ℂ :=
  fun x => (actualResidualSourceSymbol e.profile e.N e.q e.a₀ e.t₀ r L e.ρ e.mass
    e.sig e.C e.J e.i f Q x).1

noncomputable def energy (e : RecursiveAngularND n)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Ψ : ℝ → ℝ) : ℝ :=
  _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
    (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) e.a e.v Ψ
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell e.X)
      (((2:ℝ)^e.N)^(-e.mass e.a)) (e.symbol L₁ f Q e.a) z.1 z.2)
    (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell e.Y)
      (((2:ℝ)^e.N)^(-e.mass e.a)) (e.symbol L₂ g P e.a) z.1 z.2)

noncomputable def sameSymbolChildren (e : RecursiveAngularND n) (p : ℕ)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Ψ : ℝ → ℝ) : ℝ :=
  _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax e.ρ e.ρ e.a p e.v e.X e.Y
    (((2:ℝ)^e.N)^(-e.mass p)) (((2:ℝ)^e.N)^(-e.mass p)) Ψ
    (e.symbol L₁ f Q e.a) (e.symbol L₂ g P e.a)

noncomputable def graphFactor (e : RecursiveAngularND n) (p : ℕ) : ℝ :=
  ((2:ℝ)^e.N)^(-2*(e.profile p-e.profile e.a)+height e.profile e.a p+
    (e.C+36*(n+1:ℝ)+5)*e.sig)

lemma symbol_measurable (e : RecursiveAngularND n)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (r : ℕ) :
    Measurable (Function.uncurry (e.symbol L f Q r)) :=
  actualResidualSourceSymbol_measurable _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf _

lemma symbol_smooth (e : RecursiveAngularND n)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1))) : ContDiff ℝ ∞ (e.symbol L f Q r x) :=
  (actualResidualSourceSymbol e.profile e.N e.q e.a₀ e.t₀ r L e.ρ e.mass
    e.sig e.C e.J e.i f Q x).2
end RecursiveAngularND

theorem uniform_recursive_symbol_jets
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (M B total : ℕ) (hW : ∀ L∈W, L.length≤B) {sig : ℝ} (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop, ∀ e : RecursiveAngularND n,
      e.N=N → e.sig=sig → 0<e.q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → (∀ x, ‖f x‖≤1) → (∀ b∈e.fullList,L b∈W) →
      (∑ b∈e.fullList,(L b).length)≤total →
      (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      _root_.OAI.CurrentFalconer.GraphSymbolJet (e.symbol L f Q e.a) M
        (((2:ℝ)^N)^sig*max 1 ((2:ℝ)^((e.retainedList e.a).sup descriptorLength)*((2:ℝ)^N)^(-50*sig))) E := by
  obtain ⟨E,hE,h⟩ := uniform_actualResidualSourceSymbol_derivatives W M B total hW sig hsig Cq hCq
  refine ⟨E,hE,?_⟩
  filter_upwards [h] with N hN
  intro e he hs hq L f Q hf hfn hL htotal hQ
  subst N
  refine ⟨e.symbol_measurable L f hf Q e.a,e.symbol_smooth L f Q e.a,hE,?_⟩
  intro x j hj w hw
  have hh := hN e.profile e.q e.a₀ e.t₀ e.a hq L e.ρ e.mass e.C e.J e.i f Q hL htotal hfn hQ x j hj w hw
  simpa only [RecursiveAngularND.symbol,RecursiveAngularND.retainedList,hs,sourceMaskScaleND,
    Real.rpow_natCast] using hh

lemma uniform_recursive_symbol_imposes {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ e : RecursiveAngularND n, N₀≤e.N → e.sig=sig → e.J=J →
      IsFiniteMeasure e.ρ → 0<e.q → e.t₀≤e.N →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (g p : ℕ), PolicyDescriptor.parallel g p∈e.retainedList e.a →
      _root_.OAI.CurrentFalconer.TreeND.ImposesParallelTest e.ρ g p
        (_root_.OAI.CurrentFalconer.TreeND.testWidth e.N J (e.i+1) p sig)
        (((2:ℝ)^e.N)^(height e.profile g p+e.C*sig)) (e.symbol L f Q e.a) := by
  obtain ⟨N₀,hs⟩ := uniform_actualResidualSourceSymbol_support (n:=n) hsig hJ
  refine ⟨N₀,?_⟩
  intro e hN he hJe hf hq ht L f Q g p hm P hP x hx w hw hn
  have hsupp : w∈tsupport (iteratedFDeriv ℝ 0
      (actualResidualSourceSymbol e.profile e.N e.q e.a₀ e.t₀ e.a L e.ρ e.mass
        sig e.C J e.i f Q x).1) := by
    apply subset_closure
    rw [Function.mem_support,←norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    simpa only [RecursiveAngularND.symbol,he,hJe] using hn
  have hh := hs e.N hN e.ρ hf e.profile e.q e.a₀ e.t₀ e.a hq ht e.mass e.C e.i L f Q 0 x hsupp
  have hg := (hh.resolve_left (not_not.mpr hw)) (.parallel g p) hm P
    (by simpa only [descriptorAnchor,_root_.OAI.CurrentFalconer.TreeND.literal_dyadicPaths] using hP)
    (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hx)
  simpa only [descriptorGood,testWidth,_root_.OAI.CurrentFalconer.TreeND.testWidth,
    _root_.OAI.CurrentFalconer.TreeND.literal_fullParallelCount,RecursiveAngularND.profile,
    RecursiveEnvironmentND.profile] using hg.2

theorem uniform_recursive_direct_graph {sig : ℝ} (hsig : 0<sig)
    (T : ℝ) (J : ℕ) (hJ : 0<J) (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ)
    (hsupp : tsupport Ψ⊆Ioo (1/4:ℝ) 4) (hΨ0 : ∀ r,0≤Ψ r) :
    ∃ M : ℕ, ∀ (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
      (B total : ℕ), (∀ L∈W,L.length≤B) → ∀ Cq : ℝ,0≤Cq →
    ∃ E : ℝ,0≤E ∧ ∃ N₀ : ℕ, ∀ e : RecursiveAngularND n,
      N₀≤e.N → e.sig=sig → e.J=J → e.i<e.J →
      ∀ B₀ s,RegularizedProfileData e.ρ e.N B₀ s sig e.mass →
      0<e.q → ⌈10*sig*(e.N:ℝ)⌉₊<e.q → sig*(e.N:ℝ)≤e.q → 10*sig*(e.N:ℝ)≤e.q →
      e.a₀≤e.a → e.v≤e.t₀ → e.t₀≤e.N → (e.t₀:ℝ)≤(e.v:ℝ)+sig*e.N → e.a+100*e.q<e.v →
      e.v-2*sourceFarBuffer e.N ((e.retainedList e.a).sup descriptorLength) sig≤e.a →
      e.X∈dyadicPaths e.a → e.Y∈dyadicPaths e.a → 0<e.ρ (treeCell e.X) → 0<e.ρ (treeCell e.Y) →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → Measurable g → (∀ x,‖f x‖≤1) → (∀ x,‖g x‖≤1) →
      (∀ b∈e.fullList,L₁ b∈W) → (∀ b∈e.fullList,L₂ b∈W) →
      (∑ b∈e.fullList,(L₁ b).length)≤total → (∑ b∈e.fullList,(L₂ b).length)≤total →
      (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      (∀ j≤M,∀ w,‖w‖=1 → ‖iteratedFDeriv ℝ j P.1 w‖≤Cq) →
      ∃ b : PolicyDescriptor, DirectPolicyWitness e.profile e.N e.q e.a₀ e.t₀ e.a e.v sig b ∧
        e.energy L₁ L₂ f g Q P Ψ ≤ e.graphFactor (descriptorAnchor b)*
          e.sameSymbolChildren (descriptorAnchor b) L₁ L₂ f g Q P Ψ+E*((2:ℝ)^e.N)^(-T) := by
  let c₀ : ℝ := 1/(4*(n+2:ℝ))
  have hc₀ : 0<c₀ := by dsimp [c₀]; positivity
  have hcsmall : ((n+1:ℕ)+1:ℝ)*c₀≤1/2 := by
    have he : ((n+1:ℕ)+1:ℝ)*c₀=1/4 := by dsimp [c₀]; push_cast; field_simp; ring
    rw [he]; norm_num
  obtain ⟨M,C,hC,Ng,hgraph⟩ := _root_.OAI.CurrentFalconer.TreeND.graph_H_finite_jet_estimate
    (d:=n+1) hsig hc₀ hcsmall T
  obtain ⟨K,hK,hint,hder⟩ := _root_.OAI.CurrentFalconer.graph_fixed_radial_budget hΨ
    (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ψ) (hsupp.trans Ioo_subset_Icc_self)) M
  obtain ⟨Nt,htest⟩ := uniform_recursive_symbol_imposes (n:=n) hsig hJ
  refine ⟨M,?_⟩
  intro W B total hW Cq hCq
  obtain ⟨D,hD,hjets⟩ := uniform_recursive_symbol_jets W M B total hW hsig Cq hCq
  obtain ⟨Nj,hjets⟩ := Filter.eventually_atTop.mp hjets
  refine ⟨C*K*D^4,by positivity,max Ng (max Nt Nj),?_⟩
  intro e hN he hJe hi B₀ s hρ hq hceil hsigN hsig10 ha₀ hv₀ ht₀ ht hw hdir hX hY hoccX hoccY
    L₁ L₂ f g Q P hf hg hfn hgn hL₁ hL₂ htotal₁ htotal₂ hQ hP
  let := hρ.probability
  obtain ⟨b,hb⟩ := actual_direct_policy_witness e.profile hsig.le hq hceil hsigN hsig10 ht hw hdir
  refine ⟨b,hb,?_⟩
  let p := descriptorAnchor b
  let g₀ := max e.a (p-descriptorLength b)
  have hscale : (((e.retainedList e.a).sup descriptorLength : ℕ) : ℝ)=descriptorLength b := by
    exact_mod_cast hb.maximal.symm
  have hlen : (((e.retainedList e.a).sup descriptorLength : ℕ) : ℝ)≤(e.v:ℝ)-p+2*sig*e.N := by
    rw [hscale]; exact hb.length_scale
  have hdep : (p:ℝ)-e.a≤(e.v:ℝ)-p+2*sig*e.N := by
    have hh := hb.depth_scale
    rw [Nat.cast_sub hb.anchor_gt.le] at hh
    exact hh
  have hgnear : (g₀:ℝ)≤(e.a:ℝ)+2*sig*e.N := by
    have hh := hb.g_slack
    change (g₀:ℝ)-(e.a:ℝ) ≤ sig*e.N at hh
    have : 0 ≤ sig*(e.N:ℝ) := by positivity
    linarith
  have hj₁ := hjets e.N (by omega) e rfl he hq L₁ f Q hf hfn hL₁ htotal₁ hQ
  have hj₂ := hjets e.N (by omega) e rfl he hq L₂ g P hg hgn hL₂ htotal₂ hP
  have ht₁ := htest e (by omega) he hJe inferInstance hq ht₀ L₁ f Q g₀ p hb.companion
  have ht₂ := htest e (by omega) he hJe inferInstance hq ht₀ L₂ g P g₀ p hb.companion
  have hρ' := (_root_.OAI.CurrentFalconer.TreeND.literal_regularizedProfileData_iff e.ρ e.N B₀ s sig e.mass).mp hρ
  have hh := hgraph e.N (by omega) e.ρ e.ρ B₀ s s e.mass e.mass hρ' hρ' e.a p (e.v:ℝ)
    (((e.retainedList e.a).sup descriptorLength : ℕ) : ℝ) e.C K D J (e.i+1) (e.i+1) g₀ g₀ e.X e.Y Ψ
    (e.symbol L₁ f Q e.a) (e.symbol L₂ g P e.a) hb.anchor_gt
    (by exact_mod_cast hb.anchor_lt.le) (by exact_mod_cast hv₀.trans ht₀) hdep hlen hb.frequency_slack
    (le_max_left _ _) (le_max_left _ _) hb.g_lt hb.g_lt hgnear hgnear hJ (by omega) (by omega)
    (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_dyadicPaths] using hX)
    (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_dyadicPaths] using hY)
    (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hoccX)
    (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hoccY)
    hΨ (hsupp.trans Ioo_subset_Icc_self) hΨ0 hint (hder M le_rfl) hK (by simpa only [Real.rpow_natCast] using hj₁) (by simpa only [Real.rpow_natCast] using hj₂)
    (by convert ht₁ using 1; rfl) (by convert ht₂ using 1; rfl)
  have hfactor : ((2:ℝ)^e.N)^(-((_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N p-
      _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N e.a)+
      (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N p-
      _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N e.a))+
      min (_root_.OAI.PlanarFalconer.height (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N) e.a p)
      (_root_.OAI.PlanarFalconer.height (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N) e.a p)+
      (e.C+36*(n+1:ℝ)+5)*sig)=e.graphFactor p := by
    unfold RecursiveAngularND.graphFactor
    rw [he,min_self]
    congr 1
    change -((e.profile p-e.profile e.a)+(e.profile p-e.profile e.a))+height e.profile e.a p+_=_
    ring
  simp only [Nat.cast_add,Nat.cast_one] at hh
  rw [hfactor] at hh
  simpa only [RecursiveAngularND.energy,RecursiveAngularND.sameSymbolChildren,
    _root_.OAI.CurrentFalconer.TreeND.literal_treeCell,Nat.cast_add,Nat.cast_one] using hh

namespace RecursiveAngularND
noncomputable def reachedChildren (e : RecursiveAngularND n) (p : ℕ)
    (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
    (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) (Ψ : ℝ → ℝ) : ℝ :=
  _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax e.ρ e.ρ e.a p e.v e.X e.Y
    (((2:ℝ)^e.N)^(-e.mass p)) (((2:ℝ)^e.N)^(-e.mass p)) Ψ
    (e.symbol L₁ f Q p) (e.symbol L₂ g P p)

def successor (e : RecursiveAngularND n) (p : ℕ) (X Y : CellPath (n+1)) : RecursiveAngularND n :=
  {e with a:=p,X:=X,Y:=Y}
end RecursiveAngularND

theorem uniform_recursive_reached_removal
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (B total : ℕ) (hW : ∀ L∈W,L.length≤B) {sig : ℝ} (hsig : 0<sig) (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ D : ℝ,1≤D ∧ ∀ᶠ N : ℕ in atTop, ∀ e : RecursiveAngularND n,
      e.N=N → e.sig=sig → IsFiniteMeasure e.ρ → 0<e.q → ∀ p : ℕ,e.a≤p →
      ∀ (L₁ L₂ : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f g : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q P : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → Measurable g → (∀ x,‖f x‖≤1) → (∀ x,‖g x‖≤1) →
      (∀ b∈e.fullList,L₁ b∈W) → (∀ b∈e.fullList,L₂ b∈W) →
      (∑ b∈e.fullList,(L₁ b).length)≤total → (∑ b∈e.fullList,(L₂ b).length)≤total →
      (∀ w,‖w‖=1 → ‖Q.1 w‖≤Cq) → (∀ w,‖w‖=1 → ‖P.1 w‖≤Cq) →
      ∀ Ψ : ℝ → ℝ, Integrable (fun r => Ψ (r/(2:ℝ)^e.v)) → (∀ r,0≤Ψ r) →
      e.sameSymbolChildren p L₁ L₂ f g Q P Ψ≤D^(4*total)*e.reachedChildren p L₁ L₂ f g Q P Ψ := by
  obtain ⟨D,hD,hrem⟩ := actualResidual_graph_reached_removalND W B total hW hsig Cq hCq
  refine ⟨D,hD,?_⟩
  filter_upwards [hrem] with N hrem
  intro e he hs hfin hq p hap L₁ L₂ f g Q P hf hg hfn hgn hL₁ hL₂ htotal₁ htotal₂ hQ hP Ψ hiΨ hΨ
  subst N
  let := hfin
  have hcell (X Y : CellPath (n+1)) (hX : X.length=p) (hY : Y.length=p) :
      _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
        (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) p e.v Ψ
        (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell X)
          (((2:ℝ)^e.N)^(-e.mass p)) (e.symbol L₁ f Q e.a) z.1 z.2)
        (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell Y)
          (((2:ℝ)^e.N)^(-e.mass p)) (e.symbol L₂ g P e.a) z.1 z.2) ≤
      D^(4*total)*(e.successor p X Y).energy L₁ L₂ f g Q P Ψ := by
    let X' : Fin (n+1) → ℤ := fun j => (pathIndex X j:ℤ)
    let Y' : Fin (n+1) → ℤ := fun j => (pathIndex Y j:ℤ)
    have hXY : (({X'}:Finset (Fin (n+1) → ℤ)).product {Y'}).Nonempty := by simp
    have hh := hrem e.ρ e.ρ e.profile e.q e.a₀ e.t₀ e.a p hq hap L₁ L₂ e.mass e.C e.J e.i
      f g Q P hf hg hfn hgn hL₁ hL₂ htotal₁ htotal₂ hQ hP {X'} {Y'} hXY
      (((2:ℝ)^e.N)^(-e.mass p)) (((2:ℝ)^e.N)^(-e.mass p)) e.v Ψ (by simpa only [Real.rpow_natCast] using hiΨ) hΨ
    have hprod : ({X'} : Finset (Fin (n+1) → ℤ)).product {Y'} = {(X',Y')} := by ext z; simp
    simp only [Attempt4Near.graphChildMaxND,hprod,Finset.sup'_singleton] at hh
    have heX : treeCell X=Attempt4FullFar.ambientGridCell p X' := by
      unfold treeCell; rw [hX]; rfl
    have heY : treeCell Y=Attempt4FullFar.ambientGridCell p Y' := by
      unfold treeCell; rw [hY]; rfl
    change _ ≤ D^(4*total)*
      _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
        (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) p e.v Ψ
        (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell X)
          (((2:ℝ)^e.N)^(-e.mass p)) (e.symbol L₁ f Q p) z.1 z.2)
        (fun z => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ (treeCell Y)
          (((2:ℝ)^e.N)^(-e.mass p)) (e.symbol L₂ g P p) z.1 z.2)
    rw [←hs] at hh
    rw [heX,heY]
    convert hh using 1 <;> rfl
  unfold RecursiveAngularND.sameSymbolChildren RecursiveAngularND.reachedChildren
    _root_.OAI.CurrentFalconer.TreeND.graphSourceChildMax
  split_ifs with hAB
  · apply Finset.sup'_le
    intro z hz
    have hX : z.1.length=p := _root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths p z.1 |>.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).1).1).1
    have hY : z.2.length=p := _root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths p z.2 |>.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_product.mp hz).2).1).1
    have hh := hcell z.1 z.2 hX hY
    simp only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    change _ ≤ (( _root_.OAI.CurrentFalconer.TreeND.graphChildren e.ρ e.a p e.X).product
      (_root_.OAI.CurrentFalconer.TreeND.graphChildren e.ρ e.a p e.Y)).sup' hAB _
    dsimp only [RecursiveAngularND.energy,RecursiveAngularND.successor,RecursiveAngularND.symbol]
    simp only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell]
    convert (Finset.le_sup' (f:=fun z =>
      _root_.OAI.Attempt4Near.sourceAngularHND (n+1)
        (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1)))) p e.v Ψ
        (fun q => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
          (_root_.OAI.CurrentFalconer.TreeND.treeCell z.1) (((2:ℝ)^e.N)^(-e.mass p)) (e.symbol L₁ f Q p) q.1 q.2)
        (fun q => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
          (_root_.OAI.CurrentFalconer.TreeND.treeCell z.2) (((2:ℝ)^e.N)^(-e.mass p)) (e.symbol L₂ g P p) q.1 q.2)) hz) using 1; rfl
  · simp

end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

end OAI
