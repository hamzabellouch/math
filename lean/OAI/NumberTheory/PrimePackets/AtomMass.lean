import Mathlib
import OAI.NumberTheory.PrimePackets.ObservationCovers

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
namespace PrimeDegreePackets

lemma small_matrixBall_pairwise (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧
      RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (matrixBall n ρ) := by
  obtain ⟨V,hV,_,hVi,hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset
    ((matrixBall_isOpen n r).mem_nhds (one_mem_matrixBall n hr))
  obtain ⟨ρ,hρ,hρV⟩ := matrixBall_nhds_basis hV
  refine ⟨min ρ r,lt_min hρ hr,min_le_right _ _,?_⟩
  intro g hg h hh
  apply hVV
  refine Set.mul_mem_mul ?_ (hρV (matrixBall_mono (min_le_left _ _) hh))
  rw [← hVi]
  exact Set.inv_mem_inv.mpr (hρV (matrixBall_mono (min_le_left _ _) hg))

 

theorem homogeneous_name_atom_mass {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    {L r ρ : ℝ} {M : ℕ} (hL : 1 ≤ L) (hr : 0 < r) (hρr : ρ ≤ r) (hM : 1 ≤ M)
    (hdiam : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (matrixBall n ρ))
    (hexpand : (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r))
    (hstep : StepCover (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)
      (fun g h => g⁻¹*h ∈ matrixBall n r) M)
    (K : Set (X n))
    (hinj : ∀ y ∈ K, Set.InjOn (fun g => rightAction y g) (matrixBall n (L*r)))
    {α : Type*} (P : X n → α) (bad : α → Prop) [DecidablePred bad]
    (hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall n ρ, rightAction y h = z)
    (t : ℕ) (name : ℕ → α) (hfirst : ¬bad (name 0))
    (A : Set (X n))
    (hname : ∀ y ∈ A, ∀ j ≤ 2*t,
      P ((fun x => rightAction x (diagonalOneParameter ell hell 1))^[j] y) = name j)
    (hmid : ∀ y ∈ A, (fun x => rightAction x (diagonalOneParameter ell hell 1))^[t] y ∈ K)
    (B : ℝ≥0∞)
    (hTube : ∀ y ∈ K, μ ((fun w => rightAction y w) '' twoSidedTube ell hell r t) ≤ B) :
    μ A ≤ (M^((Finset.range (2*t+1)).filter fun j => bad (name j)).card : ℕ)*B := by
  by_cases hne : A.Nonempty
  · obtain ⟨x,hx⟩ := hne
    let E : Set (G n) := {g | g ∈ matrixBall n ρ ∧ rightAction x g ∈ A}
    have hE : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) E :=
      fun g hg h hh => hdiam g hg.1 h hh.1
    have hNE : ∀ g ∈ E, ∀ j ≤ 2*t,
        P ((fun y => rightAction y (diagonalOneParameter ell hell 1))^[j] (rightAction x g)) = name j :=
      fun g hg j hj => hname _ hg.2 j hj
    obtain ⟨s,hcov,hcard,hs⟩ := homogeneous_lifted_name_cover
      (diagonalOneParameter ell hell 1) hL hr hρr hM hexpand hstep K hinj P bad hfine
      x (2*t) name E hE hNE
    have hAsub : A ⊆ ⋃ F ∈ s, (fun g => rightAction x g) '' F := by
      intro y hy
      have hxname : P x = name 0 := by simpa using hname x hx 0 (by omega)
      have hyname : P y = name 0 := by simpa using hname y hy 0 (by omega)
      obtain ⟨_,_,g,hg,hxy⟩ := hfine (name 0) hfirst x hxname y hyname
      have hgE : g ∈ E := ⟨hg,hxy ▸ hy⟩
      obtain ⟨F,hF,hgF⟩ := Set.mem_iUnion₂.mp (hcov hgE)
      exact Set.mem_iUnion₂.mpr ⟨F,hF,g,hgF,hxy⟩
    have hFB : ∀ F ∈ s, μ ((fun g => rightAction x g) '' F) ≤ B := by
      intro F hF
      apply lifted_branch_mass ell hell μ hT K t B hTube x F
      · intro g hg
        exact hmid _ ((hs F hF).1 hg).2
      · simpa only [Function.iterate_zero,Set.image_id] using (hs F hF).2 0 (by omega)
      · exact (hs F hF).2 (2*t) le_rfl
    calc
      μ A ≤ μ (⋃ F ∈ s, (fun g => rightAction x g) '' F) := measure_mono hAsub
      _ ≤ ∑ F ∈ s, μ ((fun g => rightAction x g) '' F) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _F ∈ s, B := Finset.sum_le_sum hFB
      _ = s.card*B := by simp [nsmul_eq_mul]
      _ ≤ _ := by gcongr
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end PrimeDegreePackets


namespace PrimeDegreePackets

def entropyGoodSet {Y : Type*} (T : Y → Y) (K : Set Y) (ε : ℝ) (N : ℕ) : Set Y :=
  K ∩ (T^[(N-1)/2]) ⁻¹' K ∩ {x | (visitCount T Kᶜ N x : ℝ) ≤ ε*N}

lemma entropyGoodSet_measurable {Y : Type*} [MeasurableSpace Y] {T : Y → Y}
    (hT : Measurable T) {K : Set Y} (hK : MeasurableSet K) (ε : ℝ) (N : ℕ) :
    MeasurableSet (entropyGoodSet T K ε N) :=
  (hK.inter (hK.preimage (hT.iterate _))).inter
    (measurableSet_le (measurable_visitCount hT hK.compl N) measurable_const)

 

theorem entropyGoodSet_mass {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    {K : Set Y} (hK : MeasurableSet K) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 0 < N) :
    1-(2+1/ε)*μ.real Kᶜ ≤ μ.real (entropyGoodSet T K ε N) := by
  let A := entropyGoodSet T K ε N
  have hA : MeasurableSet A := entropyGoodSet_measurable hT.measurable hK ε N
  have hsub : Aᶜ ⊆ Kᶜ ∪ (T^[(N-1)/2]) ⁻¹' Kᶜ ∪
      {x | ε*N < (visitCount T Kᶜ N x : ℝ)} := by
    intro x hx
    simp only [A,entropyGoodSet,Set.mem_compl_iff,Set.mem_inter_iff,
      Set.mem_preimage,Set.mem_ofPred_eq,not_and,not_le] at hx
    by_cases hxK : x ∈ K
    · by_cases hxT : T^[(N-1)/2] x ∈ K
      · exact Or.inr (hx ⟨hxK,hxT⟩)
      · exact Or.inl (Or.inr hxT)
    · exact Or.inl (Or.inl hxK)
  have hbad : μ.real {x | ε*N < (visitCount T Kᶜ N x : ℝ)} ≤ μ.real Kᶜ/ε := by
    have H := ENNReal.toReal_mono ENNReal.ofReal_ne_top (measure_many_visits μ hT hK.compl hN hε)
    calc
      μ.real {x | ε*N < (visitCount T Kᶜ N x : ℝ)} ≤
          (ENNReal.ofReal (μ.real Kᶜ/ε)).toReal := H
      _ = μ.real Kᶜ/ε := ENNReal.toReal_ofReal (div_nonneg measureReal_nonneg hε.le)
  have hpre : μ.real ((T^[(N-1)/2]) ⁻¹' Kᶜ) = μ.real Kᶜ :=
    congrArg ENNReal.toReal ((hT.iterate _).measure_preimage hK.compl.nullMeasurableSet)
  have H : μ.real Aᶜ ≤ 2*μ.real Kᶜ+μ.real Kᶜ/ε := by
    calc
      μ.real Aᶜ ≤ μ.real (Kᶜ ∪ (T^[(N-1)/2]) ⁻¹' Kᶜ ∪
          {x | ε*N < (visitCount T Kᶜ N x : ℝ)}) := measureReal_mono hsub
      _ ≤ μ.real (Kᶜ ∪ (T^[(N-1)/2]) ⁻¹' Kᶜ) +
          μ.real {x | ε*N < (visitCount T Kᶜ N x : ℝ)} := measureReal_union_le _ _
      _ ≤ (μ.real Kᶜ+μ.real ((T^[(N-1)/2]) ⁻¹' Kᶜ))+μ.real Kᶜ/ε :=
        add_le_add (measureReal_union_le _ _) hbad
      _ = _ := by rw [hpre]; ring
  rw [measureReal_compl hA,probReal_univ] at H
  dsimp [A] at H
  have He : (2+1/ε)*μ.real Kᶜ = 2*μ.real Kᶜ+μ.real Kᶜ/ε := by ring
  rw [He]
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma tendsto_entropyMidpoint : Tendsto (fun N : ℕ => (N-1)/2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2*b+1)] with N hN
  omega

 

lemma branching_exp_bound {M b N : ℕ} (hM : 1 ≤ M) {ε δ C : ℝ}
    (hδ : 0 ≤ δ) (hC : 0 ≤ C) (hb : (b:ℝ) ≤ ε*N) :
    (M^b : ℕ)*ENNReal.ofReal (C*Real.exp (-δ*((N-1)/2 : ℕ))) ≤
      ENNReal.ofReal ((C*Real.exp δ)*Real.exp (-(δ/2-ε*Real.log M)*N)) := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hmid : (N:ℝ) ≤ 2*((N-1)/2 : ℕ)+2 := by
    exact_mod_cast (show N ≤ 2*((N-1)/2)+2 by omega)
  have hexp : (M:ℝ)^b ≤ Real.exp (ε*N*Real.log M) := by
    calc
      (M:ℝ)^b = Real.exp ((b:ℝ)*Real.log M) := by rw [Real.exp_nat_mul,Real.exp_log hM0]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hlog)
  have hE : ε*N*Real.log M-δ*((N-1)/2 : ℕ) ≤ δ-(δ/2-ε*Real.log M)*N := by
    nlinarith
  have H : (M:ℝ)^b*(C*Real.exp (-δ*((N-1)/2 : ℕ))) ≤
      (C*Real.exp δ)*Real.exp (-(δ/2-ε*Real.log M)*N) := by
    calc
      _ ≤ Real.exp (ε*N*Real.log M)*(C*Real.exp (-δ*((N-1)/2 : ℕ))) :=
        mul_le_mul_of_nonneg_right hexp (mul_nonneg hC (Real.exp_pos _).le)
      _ = C*Real.exp (ε*N*Real.log M-δ*((N-1)/2 : ℕ)) := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
        ring
      _ ≤ C*Real.exp (δ-(δ/2-ε*Real.log M)*N) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) hC
      _ = _ := by
        rw [sub_eq_add_neg, Real.exp_add, neg_mul]
        ring
  have heq : (M^b : ℕ)*ENNReal.ofReal (C*Real.exp (-δ*((N-1)/2 : ℕ))) =
      ENNReal.ofReal ((M:ℝ)^b*(C*Real.exp (-δ*((N-1)/2 : ℕ)))) := by
    conv_rhs => rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg M) b),
      ENNReal.ofReal_pow (Nat.cast_nonneg M), ENNReal.ofReal_natCast]
    simp
  rw [heq]
  exact ENNReal.ofReal_le_ofReal H

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem good_name_atom_mass {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (μ : Measure (X n))
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    {L r ρ : ℝ} {M : ℕ} (hL : 1 ≤ L) (hr : 0 < r) (hρr : ρ ≤ r) (hM : 1 ≤ M)
    (hdiam : RelationDiameter (fun g h : G n => g⁻¹*h ∈ matrixBall n r) (matrixBall n ρ))
    (hexpand : (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) '' matrixBall n r ⊆ matrixBall n (L*r))
    (hstep : StepCover (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹)
      (fun g h => g⁻¹*h ∈ matrixBall n r) M)
    (K : Set (X n))
    (hinj : ∀ y ∈ K, Set.InjOn (fun g => rightAction y g) (matrixBall n (L*r)))
    {α : Type*} (P : X n → α) (bad : α → Prop) [DecidablePred bad]
    (hbad : ∀ x, bad (P x) ↔ x ∉ K)
    (hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall n ρ, rightAction y h = z)
    {ε δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C) {N : ℕ} (hN : 0 < N)
    (hTube : ∀ y ∈ K, μ ((fun w => rightAction y w) ''
      twoSidedTube ell hell r (((N-1)/2 : ℕ) : ℝ)) ≤ ENNReal.ofReal (C*Real.exp (-δ*((N-1)/2 : ℕ))))
    (a : Fin N → α) :
    μ (entropyGoodSet (fun x => rightAction x (diagonalOneParameter ell hell 1)) K ε N ∩
        {y | orbitName (fun x => rightAction x (diagonalOneParameter ell hell 1)) P N y = a}) ≤
      ENNReal.ofReal ((C*Real.exp δ)*Real.exp (-(δ/2-ε*Real.log M)*N)) := by
  let T : X n → X n := fun x => rightAction x (diagonalOneParameter ell hell 1)
  let A := entropyGoodSet T K ε N ∩ {y | orbitName T P N y = a}
  change μ A ≤ _
  by_cases hne : A.Nonempty
  · obtain ⟨x,hx⟩ := hne
    let name : ℕ → α := fun j => P (T^[j] x)
    have hnlen : 2*((N-1)/2)+1 ≤ N := by omega
    have hname : ∀ y ∈ A, ∀ j ≤ 2*((N-1)/2), P (T^[j] y) = name j := by
      intro y hy j hj
      have H := congrFun (hy.2.trans hx.2.symm) ⟨j,by omega⟩
      exact H
    have hfirst : ¬bad (name 0) := by
      simpa only [name,Function.iterate_zero,id_eq] using (not_congr (hbad x)).mpr (not_not.mpr hx.1.1.1)
    have hmid : ∀ y ∈ A, T^[(N-1)/2] y ∈ K := fun y hy => hy.1.1.2
    have hb : (((Finset.range (2*((N-1)/2)+1)).filter fun j => bad (name j)).card : ℝ) ≤ ε*N := by
      have hsub : (Finset.range (2*((N-1)/2)+1)).filter (fun j => bad (name j)) ⊆
          (Finset.range N).filter (fun j => T^[j] x ∈ Kᶜ) := by
        intro j hj
        obtain ⟨hj0,hj1⟩ := Finset.mem_filter.mp hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp hj0; omega),?_⟩
        exact (hbad _).mp hj1
      have hc : (((Finset.range (2*((N-1)/2)+1)).filter fun j => bad (name j)).card : ℝ) ≤
          visitCount T Kᶜ N x := by
        have H := (Nat.cast_le (α := ℝ)).mpr (Finset.card_le_card hsub)
        convert H using 1; congr 2
        unfold visitCount
        congr 1
        ext j
        simp only [Finset.mem_filter]

      exact hc.trans hx.1.2
    have H := homogeneous_name_atom_mass ell hell μ hT hL hr hρr hM hdiam hexpand hstep K hinj
      P bad hfine ((N-1)/2) name hfirst A hname hmid _ hTube
    exact H.trans (branching_exp_bound hM hδ hC hb)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end PrimeDegreePackets


namespace PrimeDegreePackets

 

theorem entropy_lower_of_ordinary_balls {d : ℕ} (μ : Measure (X (d+1)))
    [IsProbabilityMeasure μ] (hball : OrdinaryBallBound (d+1) μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    (hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) μ μ)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |ell i-ell j|) :
    ENNReal.ofReal (δ/3) ≤ measureEntropy μ
      (fun x => rightAction x (diagonalOneParameter ell hell 1)) := by
  let T : X (d+1) → X (d+1) := fun x => rightAction x (diagonalOneParameter ell hell 1)
  obtain ⟨L,hL,hexpand0⟩ := diagonal_conjugation_expansion ell hell
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hexpand : ∀ r : ℝ, 0 < r →
      (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) '' matrixBall (d+1) r ⊆
        matrixBall (d+1) (L*r) := by
    simpa only [diagonalOneParameter_neg] using hexpand0
  obtain ⟨M,hM,hstep⟩ := stepCover_of_matrix_expansion
    (MulAut.conj (diagonalOneParameter ell hell 1)⁻¹) hLpos.le hexpand
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  let ε : ℝ := δ/(12*(1+Real.log M))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεlog : ε*Real.log M ≤ δ/12 := by
    have H : ε*(12*(1+Real.log M)) = δ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  let η : ℝ := 1/(5*(2+1/ε))
  have hη : 0 < η := by positivity
  obtain ⟨K,_,hK,hKsmall⟩ := (MeasurableSet.univ : MeasurableSet (Set.univ : Set (X (d+1)))).exists_isCompact_sdiff_lt
    (measure_ne_top μ Set.univ) (show ENNReal.ofReal η ≠ 0 by exact ne_of_gt (ENNReal.ofReal_pos.mpr hη))
  have hKc : μ.real Kᶜ ≤ η := by
    have H : μ Kᶜ ≤ ENNReal.ofReal η := by simpa only [compl_eq_univ_sdiff] using hKsmall.le
    have H' := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
    simpa only [measureReal_def,ENNReal.toReal_ofReal hη.le] using H'
  have hweight : 4/5 ≤ 1-(2+1/ε)*μ.real Kᶜ := by
    have H := mul_le_mul_of_nonneg_left hKc (show 0 ≤ 2+1/ε by positivity)
    have Hη : (2+1/ε)*η = 1/5 := by dsimp [η]; field_simp
    rw [Hη] at H
    linarith
  obtain ⟨r₀,hr₀,hinj₀⟩ := compact_uniform_chart_injective K hK
  let r : ℝ := min (r₀/L) (min (1/L) (1/8))
  have hr : 0 < r := lt_min (div_pos hr₀ hLpos) (lt_min (div_pos zero_lt_one hLpos) (by norm_num))
  have hLr0 : L*r ≤ r₀ := by
    have H := (le_div_iff₀ hLpos).mp (min_le_left (r₀/L) (min (1/L) (1/8)))
    simpa only [mul_comm] using H
  have hLr1 : L*r ≤ 1 := by
    have H := (le_div_iff₀ hLpos).mp ((min_le_right (r₀/L) (min (1/L) (1/8))).trans (min_le_left _ _))
    simpa only [mul_comm] using H
  have hrquarter : r < 1/4 := (le_trans (min_le_right _ _) (min_le_right _ _)).trans_lt (by norm_num)
  have hinj : ∀ x ∈ K, Set.InjOn (fun g => rightAction x g) (matrixBall (d+1) (L*r)) :=
    fun x hx => (hinj₀ x hx).mono (matrixBall_mono hLr0)
  obtain ⟨ρ,hρ,hρr,hdiam⟩ := small_matrixBall_pairwise (d+1) hr
  obtain ⟨k,P₀,hP₀,hbad₀,hfine₀⟩ := compact_finite_observation K hK hρ
  let e := Fintype.equivFin (Fin k → Bool)
  let P : X (d+1) → Fin (Fintype.card (Fin k → Bool)) := fun x => e (P₀ x)
  let bad : Fin (Fintype.card (Fin k → Bool)) → Prop := fun b => e.symm b = (fun _ => false)
  have hP : ∀ a, MeasurableSet {x | P x = a} := by
    intro a
    have H : {x | P x = a} = {x | P₀ x = e.symm a} := by
      ext x
      exact e.eq_symm_apply.symm
    rw [H]
    exact hP₀ _
  have hbad : ∀ x, bad (P x) ↔ x ∉ K := by simpa [bad,P] using hbad₀
  have hfine : ∀ b, ¬bad b → ∀ y, P y = b → ∀ z, P z = b →
      y ∈ K ∧ z ∈ K ∧ ∃ h ∈ matrixBall (d+1) ρ, rightAction y h = z := by
    intro b hb y hy z hz
    exact hfine₀ (e.symm b) hb y (by simpa [P] using congrArg e.symm hy)
      z (by simpa [P] using congrArg e.symm hz)
  obtain ⟨C,hC,hTube⟩ := tube_mass_of_ordinary_balls hball K hK ell hell hδ hr.le hrquarter hgap
  have htend : Tendsto (fun N : ℕ => ((N-1)/2 : ℕ)) atTop atTop := tendsto_entropyMidpoint
  have hTubeN := (tendsto_natCast_atTop_atTop.comp htend).eventually hTube
  let c : ℝ := δ/2-ε*Real.log M
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hsmall : ∀ᶠ N : ℕ in atTop, ∀ a : Fin N → Fin (Fintype.card (Fin k → Bool)),
      μ.real (entropyGoodSet T K ε N ∩ {y | orbitName T P N y = a}) ≤
        (C*Real.exp δ)*Real.exp (-c*N) := by
    filter_upwards [hTubeN,eventually_ge_atTop (1:ℕ)] with N hTN hN
    intro a
    have H := good_name_atom_mass (ε := ε) ell hell μ hT hL hr hρr hM hdiam (hexpand r hr)
      (hstep r hr hLr1) K hinj P bad hbad hfine hδ.le hC.le (show 0 < N by omega) hTN a
    have H' := ENNReal.toReal_mono ENNReal.ofReal_ne_top H
    change μ.real (entropyGoodSet T K ε N ∩ {y | orbitName T P N y = a}) ≤
      (ENNReal.ofReal ((C*Real.exp δ)*Real.exp (-c*N))).toReal at H'
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ (C*Real.exp δ)*Real.exp (-c*N) by positivity)] using H'
  have hw : ∀ᶠ N : ℕ in atTop, (4/5:ℝ) ≤ μ.real (entropyGoodSet T K ε N) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    exact hweight.trans (entropyGoodSet_mass μ hT hK.isClosed.measurableSet hε (by omega))
  have H := measureEntropy_lower_of_good_atoms μ hT _ P hP (entropyGoodSet T K ε)
    (fun N => entropyGoodSet_measurable hT.measurable hK.isClosed.measurableSet ε N)
    hc (show 0 < C*Real.exp δ by positivity) hw hsmall
  apply le_trans (b := ENNReal.ofReal (c*(4/5))) _ H
  apply ENNReal.ofReal_le_ofReal
  dsimp [c]
  linarith

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma diagonalOneParameter_eq_diagonalFlow {d : ℕ} (ell : Fin (d+1) → ℝ)
    (hell : ∑ i, ell i = 0) (t : ℝ) :
    diagonalOneParameter ell hell t = diagonalFlow (fun i : Fin d => ell i.castSucc*t) := by
  apply Subtype.ext
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    congr 1
    rw [← Finset.sum_mul]
    have H := hell
    rw [Fin.sum_univ_castSucc] at H
    have H' : ell (Fin.last d) = -∑ j : Fin d, ell j.castSucc := by linarith
    rw [H']
    ring
  · simp only [Fin.snoc_castSucc]

 

theorem entropy_from_ordinary_balls_dominated {d : ℕ}
    (μ ξ : Measure (X (d+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ]
    (hball : OrdinaryBallBound (d+1) μ)
    (hAξ : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) ξ = ξ)
    {c : ℝ} (hξ : ξ ≤ ENNReal.ofReal c • μ)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    {δ : ℝ} (hδ : 0 < δ) (hgap : ∀ i j, i ≠ j → δ ≤ |ell i-ell j|) :
    ENNReal.ofReal (δ/3) ≤ measureEntropy ξ
      (fun x => rightAction x (diagonalOneParameter ell hell 1)) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal c := by
    simpa only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using hξ Set.univ
  have hc : 0 < c := ENNReal.ofReal_pos.mp (lt_of_lt_of_le zero_lt_one h1)
  have hT : MeasurePreserving (fun x => rightAction x (diagonalOneParameter ell hell 1)) ξ ξ := by
    refine ⟨(continuous_rightAction _).measurable,?_⟩
    rw [diagonalOneParameter_eq_diagonalFlow]
    exact hAξ _
  exact entropy_lower_of_ordinary_balls ξ (ordinaryBallBound_of_le hball hc hξ)
    ell hell hT hδ hgap

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def regularDiagonalWeights (d : ℕ) (i : Fin (d+1)) : ℝ :=
  (i.val:ℝ) - (∑ j : Fin (d+1), (j.val:ℝ))/(d+1)

lemma regularDiagonalWeights_sum (d : ℕ) : ∑ i, regularDiagonalWeights d i = 0 := by
  simp only [regularDiagonalWeights, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [mul_div_cancel₀ _ (show (d:ℝ)+1 ≠ 0 by positivity), sub_self]

lemma regularDiagonalWeights_separated (d : ℕ) (i j : Fin (d+1)) (hij : i ≠ j) :
    1 ≤ |regularDiagonalWeights d i - regularDiagonalWeights d j| := by
  have h : i.val ≠ j.val := fun H => hij (Fin.ext H)
  have H : regularDiagonalWeights d i - regularDiagonalWeights d j = (i.val:ℝ)-j.val := by
    unfold regularDiagonalWeights
    ring
  rw [H]
  rcases lt_or_gt_of_ne h with h | h
  · have H : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
    rw [abs_of_nonpos (by linarith : (i.val:ℝ)-j.val ≤ 0)]
    linarith
  · have H : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast (show j.val+1 ≤ i.val by omega)
    rw [abs_of_nonneg (by linarith : 0 ≤ (i.val:ℝ)-j.val)]
    linarith

 

theorem positive_entropy_every_dominated_invariant {d : ℕ}
    (μ ξ : Measure (X (d+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ξ]
    (hball : OrdinaryBallBound (d+1) μ)
    (hAξ : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) ξ = ξ)
    {c : ℝ} (hξ : ξ ≤ ENNReal.ofReal c • μ) :
    0 < measureEntropy ξ (fun x => rightAction x
      (diagonalOneParameter (regularDiagonalWeights d) (regularDiagonalWeights_sum d) 1)) := by
  have H := entropy_from_ordinary_balls_dominated μ ξ hball hAξ hξ
    (regularDiagonalWeights d) (regularDiagonalWeights_sum d)
    (δ := 1) zero_lt_one (regularDiagonalWeights_separated d)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num : (0:ℝ)<1/3)) H

end PrimeDegreePackets
end
end

end OAI
