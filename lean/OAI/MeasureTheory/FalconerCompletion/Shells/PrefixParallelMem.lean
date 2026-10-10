import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.InteriorPolicy
import OAI.MeasureTheory.Falconer.Recursion.Ledger
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphHFFiniteJetEstimate
import OAI.MeasureTheory.FalconerCompletion.Graphs.LiteralDyadicPaths
import OAI.MeasureTheory.FalconerCompletion.Recursion.PrefixDepth
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixCutoff
import OAI.MeasureTheory.FalconerCompletion.Shells.PrefixSpatialLeft

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory Filter PlanarFalconer
open scoped ContDiff Topology
variable {n : ℕ}

lemma source_prefix_parallel_mem (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (ht : t ≤ N) (hw : a+100*q < t)
    (hp : 2*policyDepth A N q a t ≤ a+t) :
    PolicyDescriptor.parallel a (policyDepth A N q a t) ∈ policyDescriptorList A N q a t := by
  classical
  have hi := policyDepth_interior A hq (policyBlocks_nonempty hq ht hw)
  apply Finset.mem_biUnion.mpr
  refine ⟨(a,t),?_,?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
        le_rfl,le_rfl,hw⟩
  · apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨a,Finset.mem_Ico.mpr ⟨?_,?_⟩,rfl⟩ <;> dsimp only at * <;> omega

lemma prefix_high_graph_ranges {a p t q N : ℕ} {sig v : ℝ}
    (hsig : 0 < sig) (hq : 0 < q) (hN : 0 < N)
    (hi : a+q ≤ p ∧ p ≤ t-q) (hw : a+100*q < t)
    (hqt : sig*N ≤ q) (hp : 2*p ≤ a+t) (ht : t ≤ N)
    (hv : v ≤ t) (hhigh : (t:ℝ)-v < sig*N) :
    a < p ∧ (p:ℝ) ≤ v ∧ v ≤ N ∧
    (p:ℝ)-a ≤ v-p+2*sig*N ∧
    (((t-a)/2:ℕ):ℝ) ≤ v-p+2*sig*N ∧ 10*sig*N ≤ v-p := by
  have ha : a ≤ t := by omega
  have hp' : (2:ℝ)*p ≤ a+t := by exact_mod_cast hp
  have hw' : (a:ℝ)+100*q < t := by exact_mod_cast hw
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hsn : 0 < sig*N := mul_pos hsig hN'
  have hfloor : (2:ℝ)*(((t-a)/2:ℕ):ℝ) ≤ (t:ℝ)-a := by
    have hh : (2:ℝ)*(((t-a)/2:ℕ):ℝ) ≤ ((t-a:ℕ):ℝ) := by
      exact_mod_cast Nat.mul_div_le (t-a) 2
    rwa [Nat.cast_sub ha] at hh
  refine ⟨by omega,by linarith, hv.trans (by exact_mod_cast ht),?_,?_,?_⟩ <;> linarith

namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma prefixInverseLeft_contDiff (z : PrefixAssignment n) (x : EuclideanSpace ℝ (Fin (n+1))) :
    ContDiff ℝ ∞ (e.prefixInverseLeft z x) := by
  have h : ContDiff ℝ ∞ (actualAngularProduct e.prefixDescriptors id (prefixLeftWords z)
    e.ρ e.mass e.N e.sig e.C e.J e.i x).1 :=
    (actualAngularProduct e.prefixDescriptors id (prefixLeftWords z)
      e.ρ e.mass e.N e.sig e.C e.J e.i x).2
  convert h using 1
  funext w
  exact e.prefixInverseLeft_eq z x w

lemma prefixInverseRight_contDiff (z : PrefixAssignment n) (x : EuclideanSpace ℝ (Fin (n+1))) :
    ContDiff ℝ ∞ (e.prefixInverseRight z x) := by
  have h : ContDiff ℝ ∞ (actualAngularProduct e.prefixDescriptors id (prefixRightWords z)
    e.ρ e.mass e.N e.sig e.C e.J e.i x).1 :=
    (actualAngularProduct e.prefixDescriptors id (prefixRightWords z)
      e.ρ e.mass e.N e.sig e.C e.J e.i x).2
  convert h using 1
  funext w
  exact e.prefixInverseRight_eq z x w

lemma prefixPhasedLeft_measurable (z : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    Measurable (Function.uncurry (e.prefixPhasedLeft z ξ)) := by
  exact ((Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_continuous (n+1)
    ((2:ℝ)^e.a)⁻¹).measurable.comp (measurable_const.prodMk measurable_fst)).mul
      (e.prefixInverseLeft_measurable z)

lemma prefixPhasedRight_measurable (z : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    Measurable (Function.uncurry (e.prefixPhasedRight z ξ)) := by
  exact ((Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_continuous (n+1)
    ((2:ℝ)^e.a)⁻¹).measurable.comp (measurable_const.prodMk measurable_fst)).mul
      (e.prefixInverseRight_measurable z)

lemma prefixPhased_jets {m : ℕ} {S B : ℝ} (hB : 0 ≤ B)
    (z : PrefixAssignment n) (ξ : EuclideanSpace ℝ (Fin (n+1)))
    (hleft : ∀ x r, r ≤ m → ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ r (e.prefixInverseLeft z x) w‖ ≤ B*S^r)
    (hright : ∀ x r, r ≤ m → ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ r (e.prefixInverseRight z x) w‖ ≤ B*S^r) :
    _root_.OAI.CurrentFalconer.GraphSymbolJet (e.prefixPhasedLeft z ξ) m S B ∧
    _root_.OAI.CurrentFalconer.GraphSymbolJet (e.prefixPhasedRight z ξ) m S B := by
  constructor
  · refine ⟨e.prefixPhasedLeft_measurable z ξ,fun x => contDiff_const.mul
      (e.prefixInverseLeft_contDiff z x),hB,?_⟩
    intro x r hr w hw
    exact (symbol_const_mul_derivative_boundND ⟨e.prefixInverseLeft z x,e.prefixInverseLeft_contDiff z x⟩
      _ (le_of_eq (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_norm _ _ _ _)) r w).trans
      (hleft x r hr w hw)
  · refine ⟨e.prefixPhasedRight_measurable z ξ,fun x => contDiff_const.mul
      (e.prefixInverseRight_contDiff z x),hB,?_⟩
    intro x r hr w hw
    exact (symbol_const_mul_derivative_boundND ⟨e.prefixInverseRight z x,e.prefixInverseRight_contDiff z x⟩
      _ (le_of_eq (Attempt4PrefixShell.SpatialFourierND.spatialFourierPhase_norm _ _ _ _)) r w).trans
      (hright x r hr w hw)

lemma prefixAngularHF_graph_eq (v : ℝ) (Ψ : ℝ → ℝ) (z : PrefixAssignment n)
    (ξ : EuclideanSpace ℝ (Fin (n+1))) :
    e.prefixAngularHF v Ψ z ξ =
      _root_.OAI.Attempt4Near.sourceAngularHFND (n+1)
        (_root_.OAI.Attempt4FullFar.canonicalSphereMeasureND (EuclideanSpace ℝ (Fin (n+1))))
        e.a v Ψ e.prefixCutoff
        (fun rw => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
          (_root_.OAI.CurrentFalconer.TreeND.treeCell e.X) (((2:ℝ)^e.N)^(-e.mass e.a))
          (e.prefixPhasedLeft z ξ) rw.1 rw.2)
        (fun rw => _root_.OAI.CurrentFalconer.sourceAngularTransformND e.ρ
          (_root_.OAI.CurrentFalconer.TreeND.treeCell e.Y) (((2:ℝ)^e.N)^(-e.mass e.a))
          (e.prefixPhasedRight z ξ) rw.1 rw.2) := by
  simp only [prefixAngularHF,prefixSpatialLeft,prefixSpatialRight,
    Attempt4PrefixShell.spatialEndpointTransformND,Attempt4PrefixShell.sourceAngularHFND,
    _root_.OAI.Attempt4Near.sourceAngularHFND,Attempt4PrefixShell.sourceAngularTransformND,
    _root_.OAI.CurrentFalconer.sourceAngularTransformND,levelMass,
    _root_.OAI.CurrentFalconer.TreeND.literal_treeCell]
  rfl

lemma prefix_graph_centers {K : ℝ} (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : Attempt4FullFar.farSeparatedGridND e.a K
      (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    ‖_root_.OAI.CurrentFalconer.TreeND.treeCenter e.X-_root_.OAI.CurrentFalconer.TreeND.treeCenter e.Y‖ ≤
      (4*K)*(2:ℝ)^(-(e.a:ℝ)) := by
  rw [←_root_.OAI.CurrentFalconer.TreeND.literal_treeCenter,
    ←_root_.OAI.CurrentFalconer.TreeND.literal_treeCenter]
  change ‖ambientGridCenter e.X.length _-ambientGridCenter e.Y.length _‖ ≤ _
  rw [hX,hY,←dist_eq_norm,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
  simpa only [div_eq_mul_inv,ambientGridCenter,Attempt4FullFar.ambientGridCenter] using hs.2
end PositiveDistanceState

lemma uniform_prefixPhased_imposes {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)), N₀ ≤ e.N → e.sig=sig → e.J=J →
    IsFiniteMeasure e.ρ → 0 < e.q → e.t ≤ e.N → e.a+100*e.q < e.t →
    2*e.sourcePrefixDepth ≤ e.a+e.t → ∀ (z : PrefixAssignment n)
      (ξ : EuclideanSpace ℝ (Fin (n+1))),
    let bound := ((2:ℝ)^e.N)^(height (adjustedProfile (d:=n+1) e.mass e.N)
      e.a e.sourcePrefixDepth+e.C*sig)
    let width := _root_.OAI.CurrentFalconer.TreeND.testWidth e.N J (e.i+1) e.sourcePrefixDepth sig
    _root_.OAI.CurrentFalconer.TreeND.ImposesParallelTest e.ρ e.a e.sourcePrefixDepth width bound
      (e.prefixPhasedLeft z ξ) ∧
    _root_.OAI.CurrentFalconer.TreeND.ImposesParallelTest e.ρ e.a e.sourcePrefixDepth width bound
      (e.prefixPhasedRight z ξ) := by
  obtain ⟨N₀,hsupport⟩ := uniform_prefixInverse_support (n:=n) hsig hJ
  refine ⟨N₀,?_⟩
  intro e hN he hJe hf hq ht hw hp z ξ
  have hmem : PolicyDescriptor.parallel e.a e.sourcePrefixDepth ∈ e.prefixDescriptors :=
    source_prefix_parallel_mem _ hq ht hw hp
  have hh (x w : EuclideanSpace ℝ (Fin (n+1))) (hw : ‖w‖=1) :=
    hsupport e hN he hJe hf hq ht z 0 x w hw
  have htest (x w : EuclideanSpace ℝ (Fin (n+1)))
      (h : (x,w) ∈ endpointGood e.ρ e.mass e.N e.sig e.C e.J (e.i+1)
        (.parallel e.a e.sourcePrefixDepth))
      (P : _root_.OAI.CurrentFalconer.TreeND.CellPath (n+1))
      (hP : P ∈ _root_.OAI.CurrentFalconer.TreeND.dyadicPaths e.sourcePrefixDepth)
      (hx : x ∈ _root_.OAI.CurrentFalconer.TreeND.treeCell P) :
      (_root_.OAI.CurrentFalconer.TreeND.fullParallelCount e.ρ e.a e.sourcePrefixDepth P
        (_root_.OAI.CurrentFalconer.TreeND.testWidth e.N J (e.i+1) e.sourcePrefixDepth sig) w:ℝ) ≤
      ((2:ℝ)^e.N)^(height (adjustedProfile (d:=n+1) e.mass e.N)
        e.a e.sourcePrefixDepth+e.C*sig) := by
    have hh := h P (by simpa only [descriptorAnchor,_root_.OAI.CurrentFalconer.TreeND.literal_dyadicPaths] using hP)
      (by simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hx)
    simpa only [descriptorGood,he,hJe,testWidth,_root_.OAI.CurrentFalconer.TreeND.testWidth,
      _root_.OAI.CurrentFalconer.TreeND.literal_fullParallelCount] using hh.2
  constructor
  · intro P hP x hx w hw hn
    apply htest x w _ P hP hx
    apply (hh x w hw).1 _ _ hmem
    apply subset_closure
    rw [Function.mem_support,←norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    exact (mul_ne_zero_iff.mp hn).2
  · intro P hP x hx w hw hn
    apply htest x w _ P hP hx
    apply (hh x w hw).2 _ _ hmem
    apply subset_closure
    rw [Function.mem_support,←norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    exact (mul_ne_zero_iff.mp hn).2
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer GraphLiteralSupport.Attempt4FullFar
open scoped ContDiff
variable {n : ℕ}

theorem uniform_actual_prefix_inverse_graph (hn : 1 ≤ n)
    {sig K : ℝ} (hsig : 0 < sig) (hK : 32*(n+2:ℝ) ≤ K)
    (Jsmooth Order : ℕ) (hJ : 0 < Jsmooth) (T : ℝ) (_hT : 0 < T)
    (Ψ : ℝ → ℝ) (hΨ : ContDiff ℝ ∞ Ψ) (hsupp : tsupport Ψ ⊆ Ioo (1/4:ℝ) 4)
    (hΨ0 : ∀ r, 0 ≤ Ψ r) (_hΨ1 : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ (e : PositiveDistanceState (n+1)),
    N₀ ≤ e.N → e.sig=sig → e.J=Jsmooth → e.i < e.J →
    ∀ (B : ℕ) (s : ℝ), RegularizedProfileData e.ρ e.N B s sig e.mass →
    0 < e.q → e.t ≤ e.N → e.a+100*e.q < e.t → sig*e.N ≤ e.q →
    2*e.sourcePrefixDepth ≤ e.a+e.t →
    e.X.length=e.a → e.Y.length=e.a → 0 < e.ρ (treeCell e.X) → 0 < e.ρ (treeCell e.Y) →
    farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
    ∀ v : ℝ, v ≤ e.t → (e.t:ℝ)-v < sig*e.N →
    ∀ j ≤ Order, ∀ z ∈ GraphLiteralSupport.Attempt4PrefixShell.inverseAngularTermsND j
      (e.prefixDescriptors.disjSum e.prefixDescriptors),
    ∀ ξ : EuclideanSpace ℝ (Fin (n+1)),
      e.prefixAngularHF v Ψ z ξ ≤ e.prefixGraphFactor * e.prefixGraphChildMax v Ψ z ξ +
        C*((2:ℝ)^e.N)^(-T) := by
  classical
  let c₀ : ℝ := 1/(4*(n+2:ℝ))
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hcsmall : ((n+1:ℕ)+1:ℝ)*c₀ ≤ 1/2 := by
    have he : ((n+1:ℕ)+1:ℝ)*c₀ = 1/4 := by
      dsimp [c₀]
      push_cast
      field_simp
      ring
    rw [he]
    norm_num
  have hK0 : 0 ≤ 4*K := by
    have hn0 : (0:ℝ) ≤ n := by positivity
    nlinarith
  obtain ⟨m,C,hC,N₁,hgraph⟩ := _root_.OAI.CurrentFalconer.TreeND.graph_HF_finite_jet_estimate
    (d:=n+1) hsig hc₀ hcsmall hK0 T
  obtain ⟨BΨ,hBΨ,hintΨ,hderivΨ⟩ := _root_.OAI.CurrentFalconer.graph_fixed_radial_budget hΨ
    (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport Ψ)
      (hsupp.trans Ioo_subset_Icc_self)) m
  obtain ⟨P,hP,hcut⟩ := uniform_prefixCutoff_derivatives (d:=n+1) K
  let Pcut : ℝ := ∑ j ∈ Finset.range (m+1), P j
  have hPcut : 0 ≤ Pcut := Finset.sum_nonneg (fun j _ => hP j)
  have hPbound (j : ℕ) (hj : j ≤ m) : P j ≤ Pcut :=
    Finset.single_le_sum (fun k _ => hP k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  obtain ⟨D,hD,hder⟩ := uniform_prefixInverse_derivatives (n:=n) m Order hsig
  obtain ⟨N₂,hder⟩ := Filter.eventually_atTop.mp hder
  obtain ⟨N₃,himpose⟩ := uniform_prefixPhased_imposes (n:=n) hsig hJ
  refine ⟨C*BΨ*Pcut^2*(D^(2*Order))^4,by positivity,
    max 1 (max N₁ (max N₂ N₃)),?_⟩
  intro e he hse hJe hi B s hρ hq ht hwide hqscale hprefix hX hY hoccX hoccY hsep
    v hv hhigh j hj z hz ξ
  have hNpos : 0 < e.N := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans he)
  have hN₁ : N₁ ≤ e.N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans he
  have hN₂ : N₂ ≤ e.N := (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)).trans he
  have hN₃ : N₃ ≤ e.N := (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)).trans he
  let := hρ.probability
  have hρ' := (_root_.OAI.CurrentFalconer.TreeND.literal_regularizedProfileData_iff e.ρ e.N B s sig e.mass).mp hρ
  have hinterior := policyDepth_interior (adjustedProfile (d:=n+1) e.mass e.N) hq
    (policyBlocks_nonempty hq ht hwide)
  have hrange := prefix_high_graph_ranges hsig hq hNpos hinterior hwide hqscale hprefix ht hv hhigh
  let L : ℝ := (((e.t-e.a)/2:ℕ):ℝ)
  have hb := e.prefixPhased_jets (m:=m)
    (S:=((2:ℝ)^e.N)^sig*max 1 ((2:ℝ)^L*((2:ℝ)^e.N)^(-50*sig)))
    (by positivity : 0 ≤ D^(2*Order)) z ξ
    (fun x r hr w hw => by
      have hh := (hder e.N hN₂ e rfl hse hq j hj z hz x r hr w hw).1
      simpa only [sourceMaskScaleND,Real.rpow_natCast,L] using hh)
    (fun x r hr w hw => by
      have hh := (hder e.N hN₂ e rfl hse hq j hj z hz x r hr w hw).2
      simpa only [sourceMaskScaleND,Real.rpow_natCast,L] using hh)
  have htest := himpose e hN₃ hse hJe inferInstance hq ht hwide hprefix z ξ
  have htest₁ : _root_.OAI.CurrentFalconer.TreeND.ImposesParallelTest e.ρ e.a e.sourcePrefixDepth
      (_root_.OAI.CurrentFalconer.TreeND.testWidth e.N Jsmooth (e.i+1) e.sourcePrefixDepth sig)
      (((2:ℝ)^e.N)^(_root_.OAI.PlanarFalconer.height
        (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N)
        e.a e.sourcePrefixDepth+e.C*sig)) (e.prefixPhasedLeft z ξ) := by
    convert htest.1 using 1
    rfl
  have htest₂ : _root_.OAI.CurrentFalconer.TreeND.ImposesParallelTest e.ρ e.a e.sourcePrefixDepth
      (_root_.OAI.CurrentFalconer.TreeND.testWidth e.N Jsmooth (e.i+1) e.sourcePrefixDepth sig)
      (((2:ℝ)^e.N)^(_root_.OAI.PlanarFalconer.height
        (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N)
        e.a e.sourcePrefixDepth+e.C*sig)) (e.prefixPhasedRight z ξ) := by
    convert htest.2 using 1
    rfl
  have hX' : e.X ∈ _root_.OAI.CurrentFalconer.TreeND.dyadicPaths e.a :=
    (_root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths _ _).mpr hX
  have hY' : e.Y ∈ _root_.OAI.CurrentFalconer.TreeND.dyadicPaths e.a :=
    (_root_.OAI.CurrentFalconer.TreeND.mem_dyadicPaths _ _).mpr hY
  have hoccX' : 0 < e.ρ (_root_.OAI.CurrentFalconer.TreeND.treeCell e.X) := by
    simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hoccX
  have hoccY' : 0 < e.ρ (_root_.OAI.CurrentFalconer.TreeND.treeCell e.Y) := by
    simpa only [_root_.OAI.CurrentFalconer.TreeND.literal_treeCell] using hoccY
  have hi' : e.i+1 ≤ Jsmooth := by omega
  have hanchor : (e.a:ℝ) ≤ (e.a:ℝ)+2*sig*e.N := le_add_of_nonneg_right (by positivity)
  have hh := hgraph e.N hN₁ e.ρ e.ρ B s s e.mass e.mass hρ' hρ'
    e.a e.sourcePrefixDepth v L e.C BΨ (D^(2*Order)) Pcut Jsmooth (e.i+1) (e.i+1)
    e.a e.a e.X e.Y Ψ e.prefixCutoff (e.prefixPhasedLeft z ξ) (e.prefixPhasedRight z ξ)
    hrange.1 hrange.2.1 hrange.2.2.1 hrange.2.2.2.1 hrange.2.2.2.2.1 hrange.2.2.2.2.2
    le_rfl le_rfl hrange.1 hrange.1 hanchor hanchor hJ hi' hi'
    hX' hY' hoccX' hoccY' (e.prefix_graph_centers hX hY hsep)
    hΨ (hsupp.trans Ioo_subset_Icc_self) hΨ0 hintΨ (hderivΨ m le_rfl) hBΨ
    hb.1 hb.2 hPcut e.prefixCutoff_contDiff (fun w _ => e.prefixCutoff_norm_le w)
    (fun j hj w hw => (hcut e hsep j w hw).trans (hPbound j hj)) htest₁ htest₂
  rw [←e.prefixAngularHF_graph_eq] at hh
  have hfactor : ((2:ℝ)^e.N)^(-(
      (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N e.sourcePrefixDepth-
        _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N e.a)+
      (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N e.sourcePrefixDepth-
        _root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N e.a))+
      min (_root_.OAI.PlanarFalconer.height
        (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N) e.a e.sourcePrefixDepth)
        (_root_.OAI.PlanarFalconer.height
        (_root_.OAI.CurrentFalconer.TreeND.adjustedProfile (d:=n+1) e.mass e.N) e.a e.sourcePrefixDepth)+
      (e.C+36*(n+1:ℝ)+5)*sig) = e.prefixGraphFactor := by
    unfold PositiveDistanceState.prefixGraphFactor
    rw [hse,min_self]
    congr 1
    change -((adjustedProfile (d:=n+1) e.mass e.N e.sourcePrefixDepth-
      adjustedProfile (d:=n+1) e.mass e.N e.a)+(adjustedProfile (d:=n+1) e.mass e.N e.sourcePrefixDepth-
      adjustedProfile (d:=n+1) e.mass e.N e.a))+height (adjustedProfile (d:=n+1) e.mass e.N)
      e.a e.sourcePrefixDepth+(e.C+36*(n+1:ℝ)+5)*sig = _
    ring
  simpa only [Nat.cast_add,Nat.cast_one,hfactor,PositiveDistanceState.prefixGraphChildMax]
    using hh
end GraphLiteralSupport.CurrentFalconer.TreeND
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport.CurrentFalconer.TreeND.PositiveDistanceState
open Set MeasureTheory
variable {n : ℕ} (e : PositiveDistanceState (n+1))

noncomputable def prefixHighChildValues (Order : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) : Set ℝ :=
  insert 0 {r | ∃ j ≤ Order, ∃ z ∈ Attempt4PrefixShell.inverseAngularTermsND j
    (e.prefixDescriptors.disjSum e.prefixDescriptors),
    ∃ ξ : EuclideanSpace ℝ (Fin (n+1)), r=e.prefixGraphChildMax v Ψ z ξ}
noncomputable def prefixHighChildSup (Order : ℕ) (v : ℝ) (Ψ : ℝ → ℝ) : ℝ :=
  sSup (e.prefixHighChildValues Order v Ψ)
end GraphLiteralSupport.CurrentFalconer.TreeND.PositiveDistanceState
end
end

end OAI
