import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.Connections

namespace OAI

/-! Scale Budget for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section AveragedBinOrbitTransport
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integral_tsum_of_finite_support {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset α) (f : Ω → α → ℝ)
    (hi : ∀ x, Integrable (fun ω => f ω x) μ)
    (hs : ∀ ω x, x ∉ S → f ω x = 0) :
    (∫ ω, ∑' x, f ω x ∂μ) = ∑' x, ∫ ω, f ω x ∂μ := by
  have he (ω) : (∑' x, f ω x) = ∑ x ∈ S, f ω x := tsum_eq_sum (hs ω)
  rw [show (∫ ω, ∑' x, f ω x ∂μ) = ∫ ω, ∑ x ∈ S, f ω x ∂μ by simp only [he],
    integral_finsetSum _ (fun x _ => hi x),tsum_eq_sum (s := S) (fun x hx => by simp only [hs _ x hx,integral_zero])]

theorem binOrbitTransportMass_local (G : BondGraph V E) (hloc : LocallyFinite G)
    (n : ℕ) (ω : Set E) (x y : V) :
    let Qx := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
    let Qy := incidentSupport G hloc (finite_reachBall hloc y (2*n)).toFinset
    binOrbitTransportMass G n ω x y = binOrbitTransportMass G n (ω ∩ ((Qx∪Qy : Finset E) : Set E)) x y := by
  let Qx := incidentSupport G hloc (finite_reachBall hloc x (2*n)).toFinset
  let Qy := incidentSupport G hloc (finite_reachBall hloc y (2*n)).toFinset
  have hB := finite_local_of_subset Qx (Qx∪Qy) Finset.subset_union_left
    (fun ω => binConnectionMass G n ω x y) (fun ω => binConnectionMass_local G hloc n ω x y) ω
  have hq := finite_local_of_subset Qy (Qx∪Qy) Finset.subset_union_right
    (fun ω => binOrbitRowMass G n ω y) (fun ω => binOrbitRowMass_local G hloc n ω y) ω
  have hs := finite_local_of_subset Qx (Qx∪Qy) Finset.subset_union_left
    (fun ω => binSizeMass G n ω x) (fun ω => binSizeMass_local G hloc n ω x) ω
  exact congrArg₂ (· / ·) (congrArg₂ (· * ·) hB hq) hs

theorem binOrbitTransportMass_integrable (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (x y : V) : Integrable (fun ω => binOrbitTransportMass G n ω x y) (law p) :=
  integrable_finite_local _ p _ (fun ω => binOrbitTransportMass_local G hloc n ω x y)

theorem binOrbitTransportMass_outside (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binOrbitTransportMass G n ω x y = 0 := by
  simp only [binOrbitTransportMass,binConnectionMass_outside G n ω x y hy,zero_mul,zero_div]

noncomputable def binOrbitTransport (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V) : ℝ :=
  ∫ ω, binOrbitTransportMass G n ω x y ∂law p

theorem binOrbitTransport_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (n : ℕ) (x y : V) :
    binOrbitTransport G p n (a x) (a y) = binOrbitTransport G p n x y := by
  have hm : Measurable (fun ω => binOrbitTransportMass G n ω x y) :=
    measurable_finite_local _ _ (fun ω => binOrbitTransportMass_local G hloc n ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [binOrbitTransport,binOrbitTransportMass,binConnectionMass_covariant G hab,
    binOrbitRowMass_covariant G n _ hab,binSizeMass_covariant G n _ hab] using h.symm

theorem binOrbitTransport_outside (G : BondGraph V E) (p : unitInterval) (n : ℕ) (x y : V)
    (hy : y ∉ reachBall G x (2*n)) : binOrbitTransport G p n x y = 0 := by
  simp only [binOrbitTransport,binOrbitTransportMass_outside G n _ x y hy,integral_zero]

theorem binOrbitTransportMass_outside_column (G : BondGraph V E) (n : ℕ) (ω : Set E) (x y : V)
    (hx : x ∉ reachBall G y (2*n)) : binOrbitTransportMass G n ω x y = 0 := by
  have hB : binConnectionMass G n ω x y = 0 := by
    rw [binConnectionMass_symm]
    exact binConnectionMass_outside G n ω y x hx
  simp only [binOrbitTransportMass,hB,zero_mul,zero_div]

theorem binOrbitTransport_row_integral (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (x : V) :
    (∑' y, binOrbitTransport G p n x y) = ∫ ω, ∑' y, binOrbitTransportMass G n ω x y ∂law p := by
  symm
  apply integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
    (binOrbitTransportMass_integrable G hloc p n x)
  intro ω y hy
  exact binOrbitTransportMass_outside G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hy)

theorem integral_binOrbitRowMass (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (x : V) :
    (∫ ω, binOrbitRowMass G n ω x ∂law p) = binOrbitRow G p x n := by
  have hx : x ∈ vertexOrbit G x := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  unfold binOrbitRowMass
  rw [integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
    (fun y => by
      by_cases hy : y ∈ vertexOrbit G x
      · simp only [ite_eq_left hy]
        exact integrable_finite_local _ p _ (fun ω => binConnectionMass_local G hloc n ω x y)
      · simp only [ite_eq_right hy]; exact integrable_const (0:ℝ))
    (fun ω y hy => by
      have hz := binConnectionMass_outside G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hy)
      simp only [hz,ite_self])]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ vertexOrbit G x
  · simp only [orbitBinConnection,hx,hy,true_and,ite_true,binConnection]
  · simp only [orbitBinConnection,hy,and_false,ite_false,integral_zero]

theorem binOrbitTransport_column (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (n : ℕ) (hn : 0 < n) (y : V) :
    (∑' x, binOrbitTransport G p n x y) = binOrbitRow G p y n := by
  rw [←integral_binOrbitRowMass G hloc p n y,←show (∫ ω, ∑' x, binOrbitTransportMass G n ω x y ∂law p) =
    ∑' x, binOrbitTransport G p n x y from
      integral_tsum_of_finite_support (law p) (finite_reachBall hloc y (2*n)).toFinset _
        (fun x => binOrbitTransportMass_integrable G hloc p n x y)
        (fun ω x hx => binOrbitTransportMass_outside_column G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hx))]
  simp only [binOrbitTransportMass_column G n hn]

end AveragedBinOrbitTransport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedOrbitBinLower
attribute [local instance] Classical.propDecidable Classical.decEq

theorem binOrbitTransport_row_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p : unitInterval) (n : ℕ) (hn : 0 < n) (x : V) :
    (n:ℝ)/Fintype.card ι * clusterWindowProbability G p x n (2*n) ≤
      ∑' y, binOrbitTransport G p n x y := by
  let B := (finite_reachBall hloc x (2*n)).toFinset
  have he (ω) : (∑' y, binOrbitTransportMass G n ω x y) =
      ∑ y ∈ B, binOrbitTransportMass G n ω x y := by
    apply tsum_eq_sum
    intro y hy
    exact binOrbitTransportMass_outside G n ω x y (by simpa only [B,Set.Finite.mem_toFinset] using hy)
  have hi : Integrable (fun ω => ∑' y, binOrbitTransportMass G n ω x y) (law p) := by
    simp only [he]
    exact integrable_finsetSum B (fun y _ => binOrbitTransportMass_integrable G hloc p n x y)
  let W := {ω | ClusterWindow G x n (2*n) ω}
  have hm : MeasurableSet W := measurableSet_clusterWindow G hloc x n (2*n)
  have hl : Integrable (W.indicator (fun _ => (n:ℝ)/Fintype.card ι)) (law p) :=
    (integrable_const _).indicator hm
  calc
    _ = ∫ ω, W.indicator (fun _ => (n:ℝ)/Fintype.card ι) ω ∂law p := by
      rw [integral_indicator_const _ hm]
      simp only [smul_eq_mul,clusterWindowProbability,W,mul_comm]
    _ ≤ ∫ ω, ∑' y, binOrbitTransportMass G n ω x y ∂law p := by
      apply integral_mono hl hi
      intro ω
      exact binOrbitTransportMass_row G root hcover n hn ω x
    _ = _ := (binOrbitTransport_row_integral G hloc p n x).symm

 

theorem weighted_binOrbitRow_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p : unitInterval) (n : ℕ) (hn : 0 < n) :
    (n:ℝ)/Fintype.card ι * (∑ i, weight i * clusterWindowProbability G p (root i) n (2*n)) ≤
      ∑ i, weight i * binOrbitRow G p (root i) n := by
  have hr (x : V) : Summable (binOrbitTransport G p n x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
    intro y hy
    exact binOrbitTransport_outside G p n x y (by simpa only [Set.Finite.mem_toFinset] using hy)
  have hc (y : V) : Summable (fun x => binOrbitTransport G p n x y) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y (2*n)).toFinset)
    intro x hx
    have hz (ω) := binOrbitTransportMass_outside_column G n ω x y (by simpa only [Set.Finite.mem_toFinset] using hx)
    simp only [binOrbitTransport,hz,integral_zero]
  have ht := htr.real root weight Γ (binOrbitTransport G p n)
    (fun a ha x y => by obtain ⟨b,hab⟩ := hΓ ha; exact binOrbitTransport_covariant G hloc p hab n x y) hr hc
  calc
    _ = ∑ i, weight i * ((n:ℝ)/Fintype.card ι * clusterWindowProbability G p (root i) n (2*n)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i, weight i * ∑' y, binOrbitTransport G p n (root i) y :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (binOrbitTransport_row_lower G hloc root hcover p n hn (root i)) (hw i))
    _ = ∑ i, weight i * ∑' x, binOrbitTransport G p n x (root i) := ht
    _ = _ := by simp only [binOrbitTransport_column G hloc p n hn]

theorem exists_binOrbitRow_lower (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p : unitInterval) (n : ℕ) (hn : 0 < n) :
    ∃ i, (n:ℝ)/Fintype.card ι * (∑ j, weight j * clusterWindowProbability G p (root j) n (2*n)) ≤
      binOrbitRow G p (root i) n := by
  have h := weighted_binOrbitRow_lower G hloc root weight Γ hΓ htr (fun i => (hw i).le) hcover p n hn
  by_contra! he
  let c := (n:ℝ)/Fintype.card ι * (∑ j, weight j * clusterWindowProbability G p (root j) n (2*n))
  have hs : (∑ i, weight i * binOrbitRow G p (root i) n) < ∑ i, weight i*c := by
    apply Finset.sum_lt_sum (fun i _ => (mul_lt_mul_of_pos_left (he i) (hw i)).le)
    exact ⟨Classical.arbitrary ι,Finset.mem_univ _,mul_lt_mul_of_pos_left (he _) (hw _)⟩
  rw [←Finset.sum_mul,hw1,one_mul] at hs
  exact (not_lt_of_ge h) hs

end WeightedOrbitBinLower

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DyadicRecords
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem summable_dyadic_of_scaled_bound (π : ℕ → ℝ) (hπ : ∀ j, 0 ≤ π j)
    (α β C : ℝ) (hαβ : α < β)
    (hC : ∀ j : ℕ, (2:ℝ)^(β*(j:ℝ))*π j ≤ C) :
    Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*π j) := by
  let r := (2:ℝ)^(α-β)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hαβ)
  have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left C
  apply hs.of_nonneg_of_le (fun j => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hπ j))
  intro j
  have he : (2:ℝ)^(α*(j:ℝ)) = r^j * (2:ℝ)^(β*(j:ℝ)) := by
    rw [show r^j = (2:ℝ)^((α-β)*(j:ℝ)) by rw [Real.rpow_mul (by norm_num),Real.rpow_natCast],
      ←Real.rpow_add (by norm_num)]
    congr 1
    ring
  rw [he,mul_assoc]
  exact (mul_le_mul_of_nonneg_left (hC j) (pow_nonneg hr0 j)).trans_eq (mul_comm _ _)

theorem unbounded_scaled_dyadic (π : ℕ → ℝ) (hπ : ∀ j, 0 ≤ π j)
    (α β : ℝ) (hαβ : α < β)
    (hdiv : ¬ Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*π j)) :
    ∀ C : ℝ, ∃ j : ℕ, C < (2:ℝ)^(β*(j:ℝ))*π j := by
  intro C
  by_contra! hC
  exact hdiv (summable_dyadic_of_scaled_bound π hπ α β C hαβ hC)

 
theorem late_record_of_unbounded (f : ℕ → ℝ) (hf : ∀ C : ℝ, ∃ j, C < f j) (N : ℕ) :
    ∃ j, N < j ∧ 1 ≤ f j ∧ ∀ i ≤ j, f i ≤ f j := by
  obtain ⟨a,ha,hamax⟩ := (Finset.range (N+1)).exists_max_image f ⟨0,by simp⟩
  obtain ⟨b,hb⟩ := hf (max 1 (f a))
  obtain ⟨j,hj,hjmax⟩ := (Finset.range (b+1)).exists_max_image f ⟨0,by simp⟩
  have hb' : max 1 (f a) < f j := hb.trans_le (hjmax b (by simp))
  refine ⟨j,?_,(le_max_left _ _).trans hb'.le,?_⟩
  · by_contra! hjN
    have he := hamax j (Finset.mem_range.mpr (by omega))
    exact (not_lt_of_ge he) ((le_max_right _ _).trans_lt hb')
  · intro i hi
    exact hjmax i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega))

 

theorem finite_family_unbounded_choice {ι : Type*} [Fintype ι]
    (P : ι → ℕ → Prop) (h : ∀ N, ∃ j, N ≤ j ∧ ∃ i, P i j) :
    ∃ i, ∀ N, ∃ j, N ≤ j ∧ P i j := by
  by_contra! hnot
  choose L hL using hnot
  obtain ⟨j,hj,i,hi⟩ := h (∑ i, L i)
  have hLi : L i ≤ ∑ t, L t := Finset.single_le_sum (fun t _ => Nat.zero_le (L t)) (Finset.mem_univ i)
  exact hL i j (hLi.trans hj) hi

theorem record_dyadic_bounds (π : ℕ → ℝ) (β : ℝ) (j : ℕ)
    (hrec : ∀ i ≤ j+1, (2:ℝ)^(β*(i:ℝ))*π i ≤ (2:ℝ)^(β*((j+1:ℕ):ℝ))*π (j+1))
    (h1 : 1 ≤ (2:ℝ)^(β*((j+1:ℕ):ℝ))*π (j+1)) :
    (2:ℝ)^(-β*((j+1:ℕ):ℝ)) ≤ π (j+1) ∧ π j ≤ (2:ℝ)^β*π (j+1) := by
  have hpos : 0 < (2:ℝ)^(β*((j+1:ℕ):ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hinv : (2:ℝ)^(-β*((j+1:ℕ):ℝ)) = 1/(2:ℝ)^(β*((j+1:ℕ):ℝ)) := by
    rw [show -β*((j+1:ℕ):ℝ) = -(β*((j+1:ℕ):ℝ)) by ring,Real.rpow_neg (by norm_num)]
    simp only [one_div]
  refine ⟨?_,?_⟩
  · rw [hinv]
    exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using h1)
  · have hr := hrec j (by omega)
    have he : (2:ℝ)^(β*((j+1:ℕ):ℝ)) = (2:ℝ)^(β*(j:ℝ))*(2:ℝ)^β := by
      rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one,Real.rpow_add (by norm_num)]
    rw [he,mul_assoc] at hr
    exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _)).mp hr

end DyadicRecords

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section OrbitDyadicScales
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterWindowProbability_split (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    clusterWindowProbability G p x a c = clusterWindowProbability G p x a b + clusterWindowProbability G p x b c := by
  have he : {ω | ClusterWindow G x a c ω} =
      {ω | ClusterWindow G x a b ω} ∪ {ω | ClusterWindow G x b c ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_union,ClusterWindow]
    constructor
    · rintro ⟨hf,ha,hc⟩
      by_cases hb : (cluster G ω x).ncard < b
      · exact Or.inl ⟨hf,ha,hb⟩
      · exact Or.inr ⟨hf,by omega,hc⟩
    · rintro (⟨hf,ha,hb⟩|⟨hf,hb,hc⟩)
      · exact ⟨hf,ha,hb.trans_le hbc⟩
      · exact ⟨hf,hab.trans hb,hc⟩
  have hd : Disjoint {ω | ClusterWindow G x a b ω} {ω | ClusterWindow G x b c ω} := by
    apply Set.disjoint_left.mpr
    intro ω h₁ h₂
    exact (not_lt_of_ge h₂.2.1) h₁.2.2
  unfold clusterWindowProbability
  rw [he,measureReal_union hd (measurableSet_clusterWindow G hloc x b c)]

noncomputable def weightedWindowProbability {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ) (a b : ℕ) : ℝ :=
  ∑ i, weight i * clusterWindowProbability G p (root i) a b

theorem weightedWindowProbability_nonneg {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (a b : ℕ) :
    0 ≤ weightedWindowProbability G p root weight a b := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (clusterWindowProbability_nonneg G p (root i) a b))

theorem weightedWindowProbability_split {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    weightedWindowProbability G p root weight a c =
      weightedWindowProbability G p root weight a b + weightedWindowProbability G p root weight b c := by
  simp only [weightedWindowProbability,clusterWindowProbability_split G hloc p _ a b c hab hbc,
    mul_add,Finset.sum_add_distrib]

noncomputable def dyadicBinProbability {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ) (j : ℕ) : ℝ :=
  weightedWindowProbability G p root weight (2^j) (2^(j+1))

 

theorem orbit_dyadic_scales (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (p : unitInterval)
    (α β : ℝ) (hαβ : α < β)
    (hdiv : ¬ Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*dyadicBinProbability G p root weight j)) :
    ∃ i, ∀ N, ∃ j, N ≤ j ∧
      ((2^(j+1):ℕ):ℝ)^(-β) ≤ dyadicBinProbability G p root weight (j+1) ∧
      weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤
        (1+(2:ℝ)^β)*dyadicBinProbability G p root weight (j+1) ∧
      (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*dyadicBinProbability G p root weight (j+1) ≤
        binOrbitRow G p (root i) (2^(j+1)) := by
  let π := dyadicBinProbability G p root weight
  let f := fun j : ℕ => (2:ℝ)^(β*(j:ℝ))*π j
  have hπ : ∀ j, 0 ≤ π j := fun j => weightedWindowProbability_nonneg G p root weight (fun i => (hw i).le) _ _
  have hf := unbounded_scaled_dyadic π hπ α β hαβ hdiv
  let P := fun i j => 1 ≤ f (j+1) ∧ (∀ t ≤ j+1, f t ≤ f (j+1)) ∧
    (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*π (j+1) ≤ binOrbitRow G p (root i) (2^(j+1))
  have hpick : ∀ N, ∃ j, N ≤ j ∧ ∃ i, P i j := by
    intro N
    obtain ⟨t,ht,h1,hr⟩ := late_record_of_unbounded f hf N
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    obtain ⟨i,hi⟩ := exists_binOrbitRow_lower G hloc root weight Γ hΓ htr hw hw1 hcover p (2^(j+1)) (by positivity)
    have he : 2*2^(j+1) = 2^(j+2) := by rw [show j+2 = (j+1)+1 by omega,pow_succ]; omega
    refine ⟨j,by omega,i,h1,hr,?_⟩
    simpa only [P,π,dyadicBinProbability,weightedWindowProbability,he] using hi
  obtain ⟨i,hi⟩ := finite_family_unbounded_choice P hpick
  refine ⟨i,?_⟩
  intro N
  obtain ⟨j,hj,h1,hr,hb⟩ := hi N
  have hs := record_dyadic_bounds π β j hr h1
  refine ⟨j,hj,?_,?_,hb⟩
  · have he : (((2^(j+1):ℕ):ℝ)^(-β)) = (2:ℝ)^(-β*((j+1:ℕ):ℝ)) := by
      rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [he]
    exact hs.1
  · rw [weightedWindowProbability_split G hloc p root weight (2^j) (2^(j+1)) (2^(j+2))
      (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.pow_le_pow_right (by norm_num) (by omega))]
    change π j + π (j+1) ≤ (1+(2:ℝ)^β)*π (j+1)
    nlinarith only [hs.2]

end OrbitDyadicScales

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterSizeMomentIntegrable
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurable_cluster_ncard (G : BondGraph V E) (hloc : LocallyFinite G) (x : V) :
    Measurable (fun ω : Set E => (cluster G ω x).ncard) := by
  have hm (k : ℕ) (hk : k ≠ 0) : MeasurableSet {ω : Set E | (cluster G ω x).ncard = k} := by
    have he : {ω : Set E | (cluster G ω x).ncard = k} = {ω | ClusterWindow G x k (k+1) ω} := by
      ext ω
      constructor
      · intro h
        have hf := Set.finite_of_ncard_ne_zero (by rw [h]; exact hk)
        exact ⟨hf,by rw [h],by rw [h]; omega⟩
      · rintro ⟨hf,hl,hu⟩
        exact le_antisymm (by omega) hl
    rw [he]
    exact measurableSet_clusterWindow G hloc x k (k+1)
  have hm0 : MeasurableSet {ω : Set E | (cluster G ω x).ncard = 0} := by
    have he : {ω : Set E | (cluster G ω x).ncard = 0} =
        (⋃ k : ℕ, {ω : Set E | (cluster G ω x).ncard = k+1})ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff,Set.mem_iUnion,Set.mem_ofPred_eq,not_exists]
      constructor
      · intro h k
        omega
      · intro h
        by_contra hz
        obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
        exact h k hk
    rw [he]
    exact (MeasurableSet.iUnion (fun k => hm (k+1) (by omega))).compl
  apply measurable_to_countable
  intro ω
  change MeasurableSet {ω' | (cluster G ω' x).ncard = (cluster G ω x).ncard}
  by_cases h : (cluster G ω x).ncard = 0
  · simpa only [h] using hm0
  · exact hm _ h

 

theorem integrable_cluster_power_of_dyadic (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) (α : ℝ) (hα : 0 < α)
    (hs : Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p x (2^j) (2^(j+1)))) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p) := by
  let f := fun ω : Set E => ((cluster G ω x).ncard:ℝ)^α
  let F := fun j : ℕ => {ω | ClusterWindow G x (2^j) (2^(j+1)) ω}.indicator
    (fun _ => (2:ℝ)^(α*((j+1:ℕ):ℝ)))
  have hFm (j : ℕ) : Measurable (F j) :=
    measurable_const.indicator (measurableSet_clusterWindow G hloc x _ _)
  have hFi (j : ℕ) : Integrable (F j) (law p) :=
    (integrable_const _).indicator (measurableSet_clusterWindow G hloc x _ _)
  have hFn (j : ℕ) (ω : Set E) : 0 ≤ F j ω := by
    exact Set.indicator_nonneg (fun _ _ => (Real.rpow_pos_of_pos (by norm_num) _).le) _
  have hFe (j : ℕ) : (∫ ω, F j ω ∂law p) =
      (2:ℝ)^α * ((2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p x (2^j) (2^(j+1))) := by
    rw [integral_indicator_const _ (measurableSet_clusterWindow G hloc x _ _)]
    simp only [smul_eq_mul,clusterWindowProbability,Nat.cast_add,Nat.cast_one,mul_add,mul_one,
      Real.rpow_add (by norm_num : (0:ℝ)<2)]
    ring
  have hsum : Summable (fun j => ∫ ω, F j ω ∂law p) := by
    simp only [hFe]
    exact hs.mul_left _
  have hbound (ω : Set E) : ENNReal.ofReal (f ω) ≤ ∑' j, ENNReal.ofReal (F j ω) := by
    by_cases hz : (cluster G ω x).ncard = 0
    · simp only [f,hz,Nat.cast_zero,Real.zero_rpow hα.ne',ENNReal.ofReal_zero]
      exact bot_le
    · let j := Nat.log 2 (cluster G ω x).ncard
      have hl := Nat.pow_log_le_self 2 hz
      have hu := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (cluster G ω x).ncard
      have hb : ClusterWindow G x (2^j) (2^(j+1)) ω :=
        ⟨Set.finite_of_ncard_ne_zero hz,hl,hu⟩
      have hle : f ω ≤ (2:ℝ)^(α*((j+1:ℕ):ℝ)) := by
        have hcast : ((cluster G ω x).ncard:ℝ) ≤ ((2^(j+1):ℕ):ℝ) := by exact_mod_cast hu.le
        have h := Real.rpow_le_rpow (Nat.cast_nonneg _) hcast hα.le
        have he : (((2^(j+1):ℕ):ℝ)^α) = (2:ℝ)^(α*((j+1:ℕ):ℝ)) := by
          rw [Nat.cast_pow,Nat.cast_ofNat,←Real.rpow_natCast,←Real.rpow_mul (by norm_num)]
          congr 1
          ring
        exact h.trans_eq he
      have he : F j ω = (2:ℝ)^(α*((j+1:ℕ):ℝ)) := Set.indicator_of_mem (show ω ∈ {ω | ClusterWindow G x (2^j) (2^(j+1)) ω} from hb) _
      exact (ENNReal.ofReal_le_ofReal (hle.trans_eq he.symm)).trans
        (ENNReal.le_tsum (f := fun scale => ENNReal.ofReal (F scale ω)) j)
  have hfn (ω : Set E) : 0 ≤ f ω := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨((measurable_of_countable (fun m : ℕ => (m:ℝ)^α)).comp (measurable_cluster_ncard G hloc x)).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfn)).mpr
  have hlin : (∫⁻ ω, ∑' j, ENNReal.ofReal (F j ω) ∂law p) < ⊤ := by
    rw [lintegral_tsum (fun j => (hFm j).ennreal_ofReal.aemeasurable)]
    simp_rw [←ofReal_integral_eq_lintegral_ofReal (hFi _) (Filter.Eventually.of_forall (hFn _))]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg (hFn j)) hsum]
    exact ENNReal.ofReal_lt_top
  exact (lintegral_mono hbound).trans_lt hlin

end ClusterSizeMomentIntegrable

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedMomentScales
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_cluster_power_of_weighted_dyadic (G : BondGraph V E)
    (hloc : LocallyFinite G) {ι : Type*} [Fintype ι] (p : unitInterval)
    (root : ι → V) (weight : ι → ℝ) (hw : ∀ i, 0 < weight i)
    (α : ℝ) (hα : 0 < α)
    (hs : Summable (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*dyadicBinProbability G p root weight j))
    (i : ι) : Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p) := by
  have hle (j : ℕ) : weight i * clusterWindowProbability G p (root i) (2^j) (2^(j+1)) ≤
      dyadicBinProbability G p root weight j := by
    exact Finset.single_le_sum
      (fun t _ => mul_nonneg (hw t).le (clusterWindowProbability_nonneg G p (root t) _ _))
      (Finset.mem_univ i)
  have hs' : Summable (fun j : ℕ => weight i *
      ((2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p (root i) (2^j) (2^(j+1)))) := by
    apply hs.of_nonneg_of_le
    · intro j
      exact mul_nonneg (hw i).le (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (clusterWindowProbability_nonneg G p (root i) _ _))
    · intro j
      have h := mul_le_mul_of_nonneg_left (hle j) (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (α*(j:ℝ)))
      nlinarith only [h]
  apply integrable_cluster_power_of_dyadic G hloc p (root i) α hα
  have he : (fun j : ℕ => (2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p (root i) (2^j) (2^(j+1))) =
      (fun j : ℕ => (weight i)⁻¹ * (weight i *((2:ℝ)^(α*(j:ℝ))*clusterWindowProbability G p (root i) (2^j) (2^(j+1))))) := by
    funext j
    rw [←mul_assoc,inv_mul_cancel₀ (hw i).ne',one_mul]
  rw [he]
  exact hs'.mul_left _

 

theorem orbit_scales_of_divergent_moment (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i)) (p : unitInterval)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (hdiv : ∃ i, ¬ Integrable (fun ω => ((cluster G ω (root i)).ncard:ℝ)^α) (law p)) :
    ∃ i, ∀ N, ∃ j, N ≤ j ∧
      ((2^(j+1):ℕ):ℝ)^(-β) ≤ dyadicBinProbability G p root weight (j+1) ∧
      weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤
        (1+(2:ℝ)^β)*dyadicBinProbability G p root weight (j+1) ∧
      (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*dyadicBinProbability G p root weight (j+1) ≤
        binOrbitRow G p (root i) (2^(j+1)) := by
  apply orbit_dyadic_scales G hloc root weight Γ hΓ htr hw hw1 hcover p α β hαβ
  intro hs
  obtain ⟨i,hi⟩ := hdiv
  exact hi (integrable_cluster_power_of_weighted_dyadic G hloc p root weight hw α hα hs i)

end WeightedMomentScales
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section LogarithmicChainLength

noncomputable def logarithmicChainLength (t : ℝ) (n : ℕ) : ℕ := ⌊Real.log n / t⌋₊

theorem logarithmicChainLength_bounds (t : ℝ) (ht : 0 < t) (n : ℕ) (hn : 1 ≤ n) :
    (logarithmicChainLength t n:ℝ)*t ≤ Real.log n ∧
      Real.log n < ((logarithmicChainLength t n:ℝ)+1)*t := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_nonneg hn'
  constructor
  · exact (le_div_iff₀ ht).mp (Nat.floor_le (div_nonneg hlog ht.le))
  · exact (div_lt_iff₀ ht).mp (Nat.lt_floor_add_one (Real.log n/t))

theorem tendsto_logarithmicChainLength (t : ℝ) (ht : 0 < t) :
    Tendsto (logarithmicChainLength t) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const ht)

theorem tendsto_log_div_chainLength (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => Real.log n / logarithmicChainLength t n) atTop (nhds t) := by
  have hk : Tendsto (fun n : ℕ => (logarithmicChainLength t n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_logarithmicChainLength t ht)
  have hlim : Tendsto (fun n : ℕ => t + t/(logarithmicChainLength t n:ℝ)) atTop (nhds t) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hk)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [eventually_ge_atTop (1:ℕ),hk.eventually_gt_atTop 0] with n hn hk0
    exact (le_div_iff₀ hk0).mpr (by simpa only [mul_comm] using (logarithmicChainLength_bounds t ht n hn).1)
  · filter_upwards [eventually_ge_atTop (1:ℕ),hk.eventually_gt_atTop 0] with n hn hk0
    have h := (logarithmicChainLength_bounds t ht n hn).2.le
    apply (div_le_iff₀ hk0).mpr
    calc
      _ ≤ ((logarithmicChainLength t n:ℝ)+1)*t := h
      _ = _ := by field_simp

theorem tendsto_chainLength_div_scale (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (logarithmicChainLength t n:ℝ)/n) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => (Real.log n/(n:ℝ))/t) atTop (nhds 0) := by
    simpa only [zero_div,Function.comp_def,id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop).div_const t
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
  · exact Eventually.of_forall (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (le_div_iff₀ ht).mpr
    rw [div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hn').mpr (logarithmicChainLength_bounds t ht n hn).1

theorem eventually_chain_volume_small (t : ℝ) (ht : 0 < t) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2*logarithmicChainLength t n*M ≤ n := by
  have hlim : Tendsto (fun n : ℕ => (2*(logarithmicChainLength t n:ℝ)*M)/(n:ℝ)) atTop (nhds 0) := by
    have h := (tendsto_chainLength_div_scale t ht).const_mul (2*(M:ℝ))
    simpa only [mul_zero] using h.congr (fun n => by ring)
  filter_upwards [(tendsto_order.mp hlim).2 1 (by norm_num),eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (div_lt_iff₀ hn').mp hn
  norm_num only [one_mul] at h
  exact_mod_cast h.le

end LogarithmicChainLength
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationPolynomial

theorem amplificationMomentFactor_ge_four (k M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    4 ≤ amplificationMomentFactor k M d c a t := by
  unfold amplificationMomentFactor
  have h1 : (0:ℝ) ≤ ((k*M)+(k*M)^2+d*(k*M)^3:ℕ) := Nat.cast_nonneg _
  have h2 : (0:ℝ) ≤ (2*c*(k*M:ℕ))^2*t/a := by positivity
  linarith

theorem amplificationMomentFactor_cubic (k M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    amplificationMomentFactor k M d c a t ≤ amplificationMomentFactor 1 M d c a t * ((k:ℝ)+1)^3 := by
  let b := (2*c*(M:ℝ))^2*t/a
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hk1 : (1:ℝ) ≤ (k:ℝ)+1 := by linarith
  have h13 : (1:ℝ) ≤ ((k:ℝ)+1)^3 := one_le_pow₀ hk1
  have h1 : (k:ℝ) ≤ ((k:ℝ)+1)^3 := by
    calc
      _ ≤ (k:ℝ)+1 := by linarith
      _ = ((k:ℝ)+1)^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hk1 (by omega)
  have h2 : (k:ℝ)^2 ≤ ((k:ℝ)+1)^3 :=
    (pow_le_pow_left₀ hk (by linarith : (k:ℝ) ≤ (k:ℝ)+1) 2).trans (pow_le_pow_right₀ hk1 (by omega))
  have h3 : (k:ℝ)^3 ≤ ((k:ℝ)+1)^3 := pow_le_pow_left₀ hk (by linarith) 3
  have he (j : ℕ) : amplificationMomentFactor j M d c a t =
      4 + (M:ℝ)*j + (M:ℝ)^2*(j:ℝ)^2 + ((d:ℝ)*(M:ℝ)^3)*(j:ℝ)^3 + b*(j:ℝ)^2 := by
    simp only [amplificationMomentFactor,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,b]
    ring
  rw [he k,he 1]
  norm_num only [Nat.cast_one,one_pow,mul_one]
  have hh0 := mul_le_mul_of_nonneg_left h13 (by norm_num : (0:ℝ) ≤ 4)
  have hh1 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg M : (0:ℝ) ≤ M)
  have hh2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (M:ℝ))
  have hh3 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ (d:ℝ)*(M:ℝ)^3 by positivity)
  have hhb := mul_le_mul_of_nonneg_left h2 hb
  nlinarith only [hh0,hh1,hh2,hh3,hhb]

theorem tendsto_log_amplificationMomentFactor_div (M d : ℕ) (c a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    Tendsto (fun k : ℕ => Real.log (amplificationMomentFactor k M d c a t)/(k:ℝ)) atTop (nhds 0) := by
  let C := amplificationMomentFactor 1 M d c a t
  have hC : 0 < C := amplificationMomentFactor_pos _ _ _ _ _ _ ha ht
  have hplus : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun k : ℕ => Real.log ((k:ℝ)+1)/(k:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hplus
  have hupper : Tendsto (fun k : ℕ => (Real.log C + 3*Real.log ((k:ℝ)+1))/(k:ℝ)) atTop (nhds 0) := by
    have h := ((tendsto_const_nhds (x := Real.log C)).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))).add (hlog.const_mul 3)
    simpa only [zero_add,mul_zero,add_div,mul_div_assoc] using h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · exact Eventually.of_forall (fun k => div_nonneg
      (Real.log_nonneg (by have := amplificationMomentFactor_ge_four k M d c a t ha ht; linarith)) (Nat.cast_nonneg _))
  · exact Eventually.of_forall (fun k => by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have hh := Real.log_le_log (amplificationMomentFactor_pos k M d c a t ha ht)
        (amplificationMomentFactor_cubic k M d c a t ha ht)
      have hp : (0:ℝ) < (k:ℝ)+1 := by positivity
      simpa only [C,Real.log_mul hC.ne' (pow_pos hp 3).ne',Real.log_pow,Nat.cast_ofNat] using hh)

end AmplificationPolynomial
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationScalarBudget

theorem eventually_inverseCodeMass_budget (s ξ : ℝ) (hs : 0 ≤ s) (hξ : 0 < ξ) :
    ∀ᶠ M : ℕ in atTop, 2 ≤ M ∧ 1 ≤ (M:ℝ)^s ∧
      inverseCodeMass M ((M:ℝ)^s) ≤ (M:ℝ)^(s+ξ) := by
  have hl := (isLittleO_log_rpow_atTop hξ).bound (by norm_num : (0:ℝ) < 1/8)
  have hcast : Tendsto (fun M : ℕ => (M:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),hcast.eventually hl] with M hM hl
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le zero_lt_one hM'
  have hL : 1 ≤ (M:ℝ)^s := Real.one_le_rpow hM' hs
  refine ⟨hM,hL,?_⟩
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hM'),
    abs_of_nonneg (Real.rpow_nonneg hM0.le ξ)] at hl
  calc
    _ ≤ 8*(M:ℝ)^s*Real.log M := inverseCodeMass_le_log M _ hM hL
    _ ≤ (M:ℝ)^s*(M:ℝ)^ξ := by
      have hh := mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hM0.le s)
      nlinarith only [hh]
    _ = _ := (Real.rpow_add hM0 _ _).symm

theorem code_bound_of_logarithmic_chain (u W t : ℝ) (hu : 0 < u) (hW : 0 ≤ W)
    (ht : 0 < t) (hbudget : W ≤ u*Real.exp t) (n : ℕ) (hn : 1 ≤ n) :
    W^logarithmicChainLength t n ≤ (n:ℝ)*u^logarithmicChainLength t n := by
  let k := logarithmicChainLength t n
  have hexp : Real.exp ((k:ℝ)*t) ≤ (n:ℝ) := by
    have h := Real.exp_le_exp.mpr (logarithmicChainLength_bounds t ht n hn).1
    have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    simpa only [Real.exp_log hnp] using h
  calc
    W^k ≤ (u*Real.exp t)^k := pow_le_pow_left₀ hW hbudget _
    _ = u^k*Real.exp ((k:ℝ)*t) := by rw [mul_pow,←Real.exp_nat_mul]
    _ ≤ u^k*n := mul_le_mul_of_nonneg_left hexp (pow_nonneg hu.le _)
    _ = _ := mul_comm _ _

theorem tendsto_rpow_mul_stretched_exp (γ ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun x : ℝ => x^γ * Real.exp (-(x^ε))) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (γ/ε) 1 zero_lt_one).comp (tendsto_rpow_atTop hε)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  simp only [Function.comp_def,neg_mul,one_mul,←Real.rpow_mul hx]
  rw [mul_div_cancel₀ γ hε.ne']

end AmplificationScalarBudget
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationGoodnessDecay

theorem eventually_amplification_goodness_decay (T : ℝ) (hT : 0 < T)
    (M d : ℕ) (c a b β ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      16*amplificationMomentFactor (logarithmicChainLength T n) M d c a b *
        Real.exp (-((2*n+logarithmicChainLength T n*M:ℕ):ℝ)^ε) ≤ a*(n:ℝ)^(-β) := by
  let C := amplificationMomentFactor 1 M d c a b
  have hC : 0 < C := amplificationMomentFactor_pos _ _ _ _ _ _ ha hb
  have hd : Tendsto (fun n : ℕ => 128*C*((n:ℝ)^(β+3)*Real.exp (-(n:ℝ)^ε))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_rpow_mul_stretched_exp (β+3) ε hε).comp tendsto_natCast_atTop_atTop).const_mul (128*C)
  have hk := (tendsto_order.mp (tendsto_chainLength_div_scale T hT)).2 1 (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℕ),hk,(tendsto_order.mp hd).2 a ha] with n hn hk hd
  let k := logarithmicChainLength T n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hkn : (k:ℝ) ≤ n := by
    exact ((div_lt_iff₀ hn0).mp hk).le.trans_eq (one_mul _)
  have hQ : amplificationMomentFactor k M d c a b ≤ 8*C*(n:ℝ)^3 := by
    have hp : ((k:ℝ)+1)^3 ≤ (2*(n:ℝ))^3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    calc
      _ ≤ C*((k:ℝ)+1)^3 := amplificationMomentFactor_cubic k M d c a b ha hb
      _ ≤ C*(2*(n:ℝ))^3 := mul_le_mul_of_nonneg_left hp hC.le
      _ = _ := by ring
  have he : Real.exp (-((2*n+k*M:ℕ):ℝ)^ε) ≤ Real.exp (-(n:ℝ)^ε) := by
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hε.le
    exact_mod_cast (show n ≤ 2*n+k*M by omega)
  have hpow : 0 < (n:ℝ)^β := Real.rpow_pos_of_pos hn0 _
  rw [Real.rpow_neg hn0.le,←div_eq_mul_inv]
  apply (le_div_iff₀ hpow).mpr
  calc
    _ ≤ (16*(8*C*(n:ℝ)^3)*Real.exp (-(n:ℝ)^ε))*(n:ℝ)^β := by
      apply mul_le_mul_of_nonneg_right _ hpow.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hQ (by norm_num)) he
        (Real.exp_pos _).le (by positivity)
    _ = 128*C*((n:ℝ)^(β+3)*Real.exp (-(n:ℝ)^ε)) := by
      rw [Real.rpow_add hn0,show (n:ℝ)^(3:ℝ) = (n:ℝ)^3 by norm_cast]
      ring
    _ ≤ a := hd.le

end AmplificationGoodnessDecay
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationLogEstimates

theorem log_inv_success_le (a Q n β u : ℝ) (ha : 0 < a) (hQ : 0 < Q)
    (hn : 0 < n) (hbound : a*n^(-β)/(8*Q) ≤ u) :
    Real.log (1/u) ≤ β*Real.log n + Real.log Q + Real.log (8/a) := by
  have hl : 0 < a*n^(-β)/(8*Q) := by positivity
  have hu : 0 < u := hl.trans_le hbound
  have h := Real.log_le_log hl hbound
  rw [Real.log_div (mul_pos ha (Real.rpow_pos_of_pos hn _)).ne' (mul_pos (by norm_num) hQ).ne',
    Real.log_mul ha.ne' (Real.rpow_pos_of_pos hn _).ne',Real.log_rpow hn,
    Real.log_mul (by norm_num : (8:ℝ) ≠ 0) hQ.ne'] at h
  rw [one_div,Real.log_inv,Real.log_div (by norm_num : (8:ℝ) ≠ 0) ha.ne']
  linarith

theorem log_inv_norm_ge (r r' : ℝ) (k : ℕ) (hr : 0 < r) (hr' : 0 < r')
    (hbound : r' ≤ 2*r^k) :
    (k:ℝ)*Real.log (1/r) - Real.log 2 ≤ Real.log (1/r') := by
  have h := Real.log_le_log hr' hbound
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_pos hr _).ne',Real.log_pow] at h
  simp only [one_div,Real.log_inv]
  linarith

 

theorem eventually_amplification_log_estimates (T ξ β H : ℝ)
    (hT : 0 < T) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hH : 0 < H)
    (M d : ℕ) (c a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      let k := logarithmicChainLength T n
      β*Real.log n + Real.log (amplificationMomentFactor k M d c a b) + Real.log (8/a) ≤
        (k:ℝ)*(β+ξ)*T ∧
      Real.log ((2*n+k*M:ℕ):ℝ) ≤ (k:ℝ)*(1+ξ)*T ∧
      (k:ℝ)*(1-ξ)*H ≤ (k:ℝ)*H-Real.log 2 ∧
      2*H ≤ (k:ℝ)*(1-ξ)*H ∧ 1 ≤ k := by
  let k := logarithmicChainLength T
  have hk : Tendsto k atTop atTop := tendsto_logarithmicChainLength T hT
  have hkR : Tendsto (fun n => (k n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hk
  have hU : Tendsto (fun n : ℕ =>
      (β*Real.log n + Real.log (amplificationMomentFactor (k n) M d c a b) + Real.log (8/a))/(k n:ℝ))
      atTop (nhds (β*T)) := by
    have h1 := (tendsto_log_div_chainLength T hT).const_mul β
    have h2 := (tendsto_log_amplificationMomentFactor_div M d c a b ha hb).comp hk
    have h3 := (tendsto_const_nhds (x := Real.log (8/a))).div_atTop hkR
    simpa only [add_zero,add_div,mul_div_assoc,Function.comp_def] using (h1.add h2).add h3
  have hm : Tendsto (fun n : ℕ => (Real.log n+Real.log 3)/(k n:ℝ)) atTop (nhds T) := by
    simpa only [add_zero,add_div] using (tendsto_log_div_chainLength T hT).add
      ((tendsto_const_nhds (x := Real.log 3)).div_atTop hkR)
  have hHlim : Tendsto (fun n : ℕ => Real.log 2/(k n:ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hkR
  have hU' := (tendsto_order.mp hU).2 ((β+ξ)*T) (by nlinarith)
  have hm' := (tendsto_order.mp hm).2 ((1+ξ)*T) (by nlinarith)
  have hH' := (tendsto_order.mp hHlim).2 (ξ*H) (mul_pos hξ hH)
  filter_upwards [hU',hm',hH',hkR.eventually_ge_atTop (2/(1-ξ)),
    hk.eventually_ge_atTop 1,eventually_ge_atTop (1:ℕ),eventually_chain_volume_small T hT M]
    with n hUn hmn hHn hklarge hk1 hn hvol
  have hkp : (0:ℝ) < k n := by exact_mod_cast (show 0 < k n by omega)
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcap : (2*n+k n*M:ℕ) ≤ 3*n := by
    dsimp [k] at *
    rw [Nat.mul_assoc] at hvol
    omega
  have hcap0 : (0:ℝ) < (2*n+k n*M:ℕ) := by exact_mod_cast (show 0 < 2*n+k n*M by omega)
  refine ⟨?_,?_,?_,?_,hk1⟩
  · have h := (div_lt_iff₀ hkp).mp hUn
    nlinarith only [h]
  · calc
      _ ≤ Real.log (3*(n:ℝ)) := Real.log_le_log hcap0 (by exact_mod_cast hcap)
      _ = Real.log n + Real.log 3 := by rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hnp.ne']; ring
      _ ≤ _ := by have h := (div_lt_iff₀ hkp).mp hmn; nlinarith only [h]
  · have h := (div_lt_iff₀ hkp).mp hHn
    nlinarith only [h]
  · have h := (div_le_iff₀ (sub_pos.mpr hξ1)).mp hklarge
    have hh := mul_le_mul_of_nonneg_right h hH.le
    nlinarith only [hh]

end AmplificationLogEstimates
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section AsymptoticAmplificationStep
attribute [local instance] Classical.propDecidable Classical.decEq
namespace LocalEndpointRule
variable {G : BondGraph V E} {hloc : LocallyFinite G} {M : ℕ} {L : ℝ}

 

theorem asymptotic_amplification_step [Nonempty V] [Nonempty E]
    (hconn : Connected G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (q : LocalEndpointRule G hloc (vertexOrbit G (root i₀)) M L) (hL : 1 ≤ L)
    (p : unitInterval) (hp : (p:ℝ) < 1) (d : ℕ) (hdeg : ∀ x, degree G x ≤ d)
    (hu : 0 < q.successProbability p (root i₀))
    (a b β ε ξ T : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε < 1/2) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hT : 0 < T)
    (hbudget : inverseCodeMass M L ≤ q.successProbability p (root i₀)*Real.exp T)
    (A : Hilbert V →L[ℂ] Hilbert V) (hApos : 0 < ‖A‖)
    (hH : 0 < Real.log (1/‖A‖))
    (hA : ∀ x y, matrixCoeff A x y = (q.normalizedKernel (root i₀) p x y : ℂ)) :
    ∀ᶠ n : ℕ in atTop, ∀ π : ℝ,
      (n:ℝ)^(-β) ≤ π →
      a*n*π ≤ binOrbitRow G p (root i₀) n →
      clusterWindowProbability G p (root i₀) (n-logarithmicChainLength T n*M) (2*n) ≤ b*π →
      ∃ q' : LocalEndpointRule G hloc (vertexOrbit G (root i₀))
          (2*n+logarithmicChainLength T n*M) (((2*n+logarithmicChainLength T n*M:ℕ):ℝ)^(1/2+ε)),
        0 < q'.successProbability p (root i₀) ∧
        Real.log (1/q'.successProbability p (root i₀)) ≤ (logarithmicChainLength T n:ℝ)*(β+ξ)*T ∧
        Real.log ((2*n+logarithmicChainLength T n*M:ℕ):ℝ) ≤ (logarithmicChainLength T n:ℝ)*(1+ξ)*T ∧
        ∃ A' : Hilbert V →L[ℂ] Hilbert V, 0 < ‖A'‖ ∧
          (logarithmicChainLength T n:ℝ)*(1-ξ)*Real.log (1/‖A‖) ≤ Real.log (1/‖A'‖) ∧
          2*Real.log (1/‖A‖) ≤ Real.log (1/‖A'‖) ∧
          (∀ x y, matrixCoeff A' x y = (q'.normalizedKernel (root i₀) p x y : ℂ)) ∧
          1 ≤ logarithmicChainLength T n := by
  let k := logarithmicChainLength T
  let cap := fun n => 2*n+k n*M
  have hcap : Tendsto cap atTop atTop :=
    tendsto_atTop_mono (fun n => show n ≤ cap n by dsimp [cap]; omega) tendsto_id
  have hgood := hcap.eventually (bad_goodness_stretched_exp G hloc hqt p hp ε hε hε1)
  have hdecay := eventually_amplification_goodness_decay T hT M d c a b β ε ha hb hε
  have hlogs := eventually_amplification_log_estimates T ξ β (Real.log (1/‖A‖))
    hT hξ hξ1 hH M d c a b ha hb
  filter_upwards [hgood,hdecay,hlogs,eventually_ge_atTop (1:ℕ)] with n hgood hdecay hlogs hn
  intro π hπ hbin hwindow
  have hn0 : 0 < n := by omega
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hπ0 : 0 < π := (Real.rpow_pos_of_pos hnR (-β)).trans_le hπ
  have hQ : 0 < amplificationMomentFactor (k n) M d c a b := amplificationMomentFactor_pos _ _ _ _ _ _ ha hb
  have hcoden : inverseCodeMass M L^(k n) ≤ n*q.successProbability p (root i₀)^(k n) := by
    apply code_bound_of_logarithmic_chain _ _ _ hu _ hT hbudget n hn
    unfold inverseCodeMass
    exact add_nonneg zero_le_one (Finset.sum_nonneg (fun l _ => gapWeight_nonneg L (by linarith) l))
  have hbad : 16*amplificationMomentFactor (k n) M d c a b *
      (law p).real {ω | CappedBadGoodness G ω (root i₀) (cap n) ((cap n:ℝ)^(1/2+ε))} ≤ a*π := by
    calc
      _ ≤ 16*amplificationMomentFactor (k n) M d c a b * Real.exp (-(cap n:ℝ)^ε) :=
        mul_le_mul_of_nonneg_left (hgood (root i₀) p le_rfl) (by positivity)
      _ ≤ a*(n:ℝ)^(-β) := hdecay
      _ ≤ _ := mul_le_mul_of_nonneg_left hπ ha.le
  obtain ⟨q',hup,A',hAp,hAr,hA'⟩ := q.quantitative_amplification_step hconn root weight Γ hΓ htr hcov
    hw hw1 c hc hmin i₀ hw₀ hL p (k n) n d hn0 hdeg hu a b π ((cap n:ℝ)^(1/2+ε))
    ha hb hπ0 hbin hwindow hcoden hbad A hA
  have hup0 : 0 < q'.successProbability p (root i₀) := (by positivity : 0 < a*π/(8*amplificationMomentFactor (k n) M d c a b)).trans_le hup
  have hulo : a*(n:ℝ)^(-β)/(8*amplificationMomentFactor (k n) M d c a b) ≤ q'.successProbability p (root i₀) := by
    apply le_trans _ hup
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hπ ha.le) (by positivity)
  have hulo' := log_inv_success_le a (amplificationMomentFactor (k n) M d c a b) (n:ℝ) β
    (q'.successProbability p (root i₀)) ha hQ hnR hulo
  have hH' := log_inv_norm_ge ‖A‖ ‖A'‖ (k n) hApos hAp hAr
  exact ⟨q',hup0,hulo'.trans hlogs.1,hlogs.2.1,A',hAp,hlogs.2.2.1.trans hH',
    hlogs.2.2.2.1.trans (hlogs.2.2.1.trans hH'),hA',hlogs.2.2.2.2⟩

end LocalEndpointRule
end AsymptoticAmplificationStep
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section WeightedScaleWindow
attribute [local instance] Classical.propDecidable Classical.decEq

theorem weightedWindowProbability_term_le {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (i : ι) (a b : ℕ) :
    weight i * clusterWindowProbability G p (root i) a b ≤ weightedWindowProbability G p root weight a b :=
  Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (clusterWindowProbability_nonneg G p (root j) a b)) (Finset.mem_univ i)

theorem orbit_scale_window_bound {ι : Type*} [Fintype ι]
    (G : BondGraph V E) (p : unitInterval) (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (i : ι) (hi : 0 < weight i)
    (j k M : ℕ) (hvol : 2*k*M ≤ 2^(j+1)) (β π : ℝ)
    (hwindow : weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤ (1+(2:ℝ)^β)*π) :
    clusterWindowProbability G p (root i) (2^(j+1)-k*M) (2*2^(j+1)) ≤
      ((1+(2:ℝ)^β)/weight i)*π := by
  have he : 2^(j+1) = 2*2^j := by rw [pow_succ]; omega
  have he' : 2*2^(j+1) = 2^(j+2) := by rw [show j+2 = (j+1)+1 by omega,pow_succ]; omega
  have hl : 2^j ≤ 2^(j+1)-k*M := by
    rw [he,Nat.mul_assoc] at hvol
    rw [he]
    omega
  have hmono := clusterWindowProbability_mono G p (root i) hl (le_of_eq he')
  have hterm := weightedWindowProbability_term_le G p root weight hw i (2^j) (2^(j+2))
  have hb := (mul_le_mul_of_nonneg_left hmono hi.le).trans (hterm.trans hwindow)
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hi).mpr (by simpa only [mul_comm] using hb)

theorem tendsto_dyadic_scale : Tendsto (fun j : ℕ => 2^(j+1)) atTop atTop :=
  tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (j+1).lt_two_pow_self.le) tendsto_id

end WeightedScaleWindow
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EndpointProfile

 

structure EndpointProfile (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (s : ℝ) where
  cap : ℕ
  rule : LocalEndpointRule G hloc (vertexOrbit G o) cap ((cap:ℝ)^s)
  success_pos : 0 < rule.successProbability p o
  op : Hilbert V →L[ℂ] Hilbert V
  norm_pos : 0 < ‖op‖
  coeff : ∀ x y, matrixCoeff op x y = (rule.normalizedKernel o p x y : ℂ)

namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p : unitInterval} {o : V} {s : ℝ}

noncomputable def U (q : EndpointProfile G hloc p o s) : ℝ := Real.log (1/q.rule.successProbability p o)
noncomputable def m (q : EndpointProfile G hloc p o s) : ℝ := Real.log q.cap
noncomputable def H (q : EndpointProfile G hloc p o s) : ℝ := Real.log (1/‖q.op‖)
noncomputable def cost (q : EndpointProfile G hloc p o s) (ξ : ℝ) : ℝ := q.U+(s+ξ)*q.m

theorem U_nonneg (q : EndpointProfile G hloc p o s) : 0 ≤ q.U := by
  unfold U
  rw [one_div,Real.log_inv]
  have h := Real.log_nonpos q.success_pos.le (q.rule.successProbability_le_one p o)
  linarith

theorem m_pos (q : EndpointProfile G hloc p o s) (hcap : 2 ≤ q.cap) : 0 < q.m := by
  exact Real.log_pos (by exact_mod_cast (show 1 < q.cap by omega))

theorem cost_pos (q : EndpointProfile G hloc p o s) (hcap : 2 ≤ q.cap)
    (ξ : ℝ) (hsξ : 0 < s+ξ) : 0 < q.cost ξ := by
  exact add_pos_of_nonneg_of_pos q.U_nonneg (mul_pos hsξ (q.m_pos hcap))

theorem exp_cost_identity (q : EndpointProfile G hloc p o s) (hcap : 0 < q.cap) (ξ : ℝ) :
    q.rule.successProbability p o * Real.exp (q.cost ξ) = (q.cap:ℝ)^(s+ξ) := by
  have hcp : (0:ℝ) < q.cap := Nat.cast_pos.mpr hcap
  simp only [cost,U,m,Real.exp_add,Real.exp_log (one_div_pos.mpr q.success_pos)]
  calc
    _ = Real.exp ((s+ξ)*Real.log q.cap) := by field_simp [ne_of_gt q.success_pos]
    _ = _ := by rw [Real.rpow_def_of_pos hcp]; congr 1; ring

end EndpointProfile

variable [Countable V] [Countable E] [Nonempty V]

theorem starting_endpoint_profile (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω (root i₀)).Finite)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (M₀ : ℕ) :
    ∃ q : EndpointProfile G hloc p (root i₀) (1/2+ε), M₀ ≤ q.cap ∧ 1 < q.H := by
  obtain ⟨M,hM,q,hq,A,hAp,hAn,hA⟩ := nonamenable_starting_endpoint_rule G hloc hqt hh p hp hp1
    root weight Γ hΓ htr hw hw1 i₀ hw₀ hfin ε hε hε1 (Real.exp (-2)) (Real.exp_pos _) M₀
  refine ⟨⟨M,q,hq,A,hAp,hA⟩,hM,?_⟩
  have h := Real.log_lt_log hAp hAn
  rw [Real.log_exp] at h
  change 1 < Real.log (1/‖A‖)
  rw [one_div,Real.log_inv]
  linarith

end EndpointProfile

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section EndpointProfileStep
attribute [local instance] Classical.propDecidable Classical.decEq

namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G}

theorem amplify_at_scales [Nonempty V] [Nonempty E]
    (hconn : Connected G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (i : ι) (p : unitInterval) (hp : (p:ℝ) < 1)
    (d : ℕ) (hdeg : ∀ x, degree G x ≤ d)
    (ε ξ β : ℝ) (hε : 0 < ε) (hε1 : ε < 1/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hscales : ∀ N, ∃ j, N ≤ j ∧
      ((2^(j+1):ℕ):ℝ)^(-β) ≤ dyadicBinProbability G p root weight (j+1) ∧
      weightedWindowProbability G p root weight (2^j) (2^(j+2)) ≤
        (1+(2:ℝ)^β)*dyadicBinProbability G p root weight (j+1) ∧
      (((2^(j+1):ℕ):ℝ)/Fintype.card ι)*dyadicBinProbability G p root weight (j+1) ≤
        binOrbitRow G p (root i) (2^(j+1)))
    (q : EndpointProfile G hloc p (root i) (1/2+ε)) (hM : 2 ≤ q.cap)
    (hL : 1 ≤ (q.cap:ℝ)^(1/2+ε))
    (hbudget : inverseCodeMass q.cap ((q.cap:ℝ)^(1/2+ε)) ≤ (q.cap:ℝ)^(1/2+ε+ξ))
    (hH : 0 < q.H) (N : ℕ) :
    ∃ (q' : EndpointProfile G hloc p (root i) (1/2+ε)) (k : ℕ),
      N ≤ q'.cap ∧ 1 ≤ k ∧
      q'.U ≤ (k:ℝ)*(β+ξ)*q.cost ξ ∧
      q'.m ≤ (k:ℝ)*(1+ξ)*q.cost ξ ∧
      (k:ℝ)*(1-ξ)*q.H ≤ q'.H ∧ 2*q.H ≤ q'.H := by
  let a : ℝ := 1/Fintype.card ι
  let b : ℝ := (1+(2:ℝ)^β)/weight i
  let T := q.cost ξ
  have ht : 0 < T := q.cost_pos hM ξ (by linarith)
  have hcard : (0:ℝ) < Fintype.card ι := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
  have ha : 0 < a := one_div_pos.mpr hcard
  have hb : 0 ≤ b := div_nonneg (by positivity) (hw i).le
  have hbudget' : inverseCodeMass q.cap ((q.cap:ℝ)^(1/2+ε)) ≤
      q.rule.successProbability p (root i)*Real.exp T := by
    rw [q.exp_cost_identity (by omega) ξ]
    exact hbudget
  have hstep := q.rule.asymptotic_amplification_step hconn hqt root weight Γ hΓ htr hcov
    (fun i => (hw i).le) hw1 c hc hmin i (hw i) hL p hp d hdeg q.success_pos
    a b β ε ξ T ha hb hε hε1 hξ hξ1 ht hbudget' q.op q.norm_pos hH q.coeff
  have hvol := eventually_chain_volume_small T ht q.cap
  have he := tendsto_dyadic_scale.eventually (hstep.and (hvol.and (eventually_ge_atTop N)))
  obtain ⟨J,hJ⟩ := eventually_atTop.1 he
  obtain ⟨j,hj,hπ,hwide,hbin⟩ := hscales J
  obtain ⟨hs,hvol,hN⟩ := hJ j hj
  have hwin := orbit_scale_window_bound G p root weight (fun i => (hw i).le) i (hw i)
    j (logarithmicChainLength T (2^(j+1))) q.cap hvol β _ hwide
  have hbin' : a*(2^(j+1):ℕ)*dyadicBinProbability G p root weight (j+1) ≤
      binOrbitRow G p (root i) (2^(j+1)) := by
    dsimp [a]
    simpa only [div_eq_mul_inv,one_mul,mul_comm (_⁻¹)] using hbin
  obtain ⟨q',hup,hU,hm,A',hAp,hH',hH'',hA',hk⟩ := hs _ hπ hbin' hwin
  refine ⟨⟨_,q',hup,A',hAp,hA'⟩,_,?_,hk,hU,hm,hH',hH''⟩
  change N ≤ 2*2^(j+1)+logarithmicChainLength T (2^(j+1))*q.cap
  omega

end EndpointProfile
end EndpointProfileStep

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open Filter
section AmplificationContraction

noncomputable def amplificationContraction (β s ξ : ℝ) : ℝ :=
  (β+ξ+(s+ξ)*(1+ξ))/(1-ξ)

theorem exists_amplification_contraction (β s : ℝ) (hβ : 0 ≤ β) (hs : 0 ≤ s)
    (hsmall : β+s < 1) : ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧
      0 ≤ amplificationContraction β s ξ ∧ amplificationContraction β s ξ < 1 := by
  have hd : 0 < 4+s := by linarith
  have hδ : 0 < (1-(β+s))/(4+s) := div_pos (by linarith) hd
  obtain ⟨ξ,hξ,hξupper⟩ := exists_between (lt_min zero_lt_one hδ)
  have hξ1 := hξupper.trans_le (min_le_left _ _)
  have hprod : ξ*(4+s) < 1-(β+s) := (lt_div_iff₀ hd).mp (hξupper.trans_le (min_le_right _ _))
  have hx2 : ξ^2 < ξ := by nlinarith [mul_pos hξ (sub_pos.mpr hξ1)]
  refine ⟨ξ,hξ,hξ1,?_,?_⟩
  · unfold amplificationContraction
    positivity
  · unfold amplificationContraction
    apply (div_lt_one (by linarith : 0 < 1-ξ)).mpr
    nlinarith

 

theorem amplification_cost_contraction (t t' H H' β s ξ : ℝ) (k : ℕ)
    (ht : 0 ≤ t) (hH : 0 < H) (hξ1 : ξ < 1) (hk : 1 ≤ k)
    (hC : 0 ≤ amplificationContraction β s ξ)
    (ht' : t' ≤ (k:ℝ)*(β+ξ+(s+ξ)*(1+ξ))*t)
    (hH' : (k:ℝ)*(1-ξ)*H ≤ H') :
    t'/H' ≤ amplificationContraction β s ξ*(t/H) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hd : 0 < (k:ℝ)*(1-ξ)*H := mul_pos (mul_pos hk0 (by linarith)) hH
  have hH'p := hd.trans_le hH'
  apply (div_le_iff₀ hH'p).mpr
  have he : (k:ℝ)*(β+ξ+(s+ξ)*(1+ξ))*t =
      amplificationContraction β s ξ*(t/H)*((k:ℝ)*(1-ξ)*H) := by
    unfold amplificationContraction
    field_simp [hH.ne', (sub_pos.mpr hξ1).ne']
  rw [he] at ht'
  exact ht'.trans (mul_le_mul_of_nonneg_left hH' (mul_nonneg hC (div_nonneg ht hH.le)))

namespace EndpointProfile
variable {G : BondGraph V E} {hloc : LocallyFinite G} {p : unitInterval} {o : V} {s : ℝ}

theorem cost_contraction (q q' : EndpointProfile G hloc p o s) (β ξ : ℝ) (k : ℕ)
    (hM : 2 ≤ q.cap) (hsξ : 0 < s+ξ) (hH : 0 < q.H) (hξ1 : ξ < 1) (hk : 1 ≤ k)
    (hC : 0 ≤ amplificationContraction β s ξ)
    (hU : q'.U ≤ (k:ℝ)*(β+ξ)*q.cost ξ)
    (hm : q'.m ≤ (k:ℝ)*(1+ξ)*q.cost ξ)
    (hH' : (k:ℝ)*(1-ξ)*q.H ≤ q'.H) :
    q'.cost ξ/q'.H ≤ amplificationContraction β s ξ*(q.cost ξ/q.H) := by
  apply amplification_cost_contraction _ _ _ _ β s ξ k (q.cost_pos hM ξ hsξ).le hH hξ1 hk hC _ hH'
  unfold cost at *
  have hh := mul_le_mul_of_nonneg_left hm hsξ.le
  nlinarith only [hU,hh]

theorem total_cost_le (q : EndpointProfile G hloc p o s) (hM : 2 ≤ q.cap)
    (ξ : ℝ) (hsξ : 0 < s+ξ) : q.U+q.m ≤ (1+1/(s+ξ))*q.cost ξ := by
  have hm := (q.m_pos hM).le
  have hU := q.U_nonneg
  have hU' : q.U ≤ q.cost ξ := by unfold cost; nlinarith
  have hm' : q.m ≤ q.cost ξ/(s+ξ) := by
    apply (le_div_iff₀ hsξ).mpr
    unfold cost
    nlinarith
  calc
    _ ≤ q.cost ξ+q.cost ξ/(s+ξ) := add_le_add hU' hm'
    _ = _ := by ring

end EndpointProfile
end AmplificationContraction

end Percolation

end OAI
