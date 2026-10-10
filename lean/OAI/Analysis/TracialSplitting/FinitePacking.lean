import OAI.Analysis.TracialSplitting.PackingEstimates

namespace OAI

universe uA uD uI

noncomputable section

namespace CurrentMain

section

open scoped ComplexOrder

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [CStarAlgebra D]

structure PositiveDiagonal (A : Type uA) [CStarAlgebra A] (K : Finset (unitary A)) (μ : ℝ) where
  size : ℕ
  weight : Fin size → ℝ
  coefficient : Fin size → A
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum : ∑ i, weight i = 1
  contractive : ∀ i, ‖coefficient i‖ ≤ 1
  defect : ‖1 - weightedAverage weight coefficient 1‖ < μ
  commutator : ∀ x ∈ K, ‖diagonalCommutator weight coefficient (x : A)‖ < μ

variable [PartialOrder D] [StarOrderedRing D]

lemma traceTwoNorm_sub_swap (τ : Pureness.TracialState D) (a b : D) :
    traceTwoNorm τ (a - b) = traceTwoNorm τ (b - a) := by
  calc
    _ = traceTwoNorm τ (-(b - a)) := by rw [neg_sub]
    _ = _ := traceTwoNorm_neg τ _

namespace OrthogonalProjectionPair

def zero : OrthogonalProjectionPair D where
  left := 0
  right := 0
  left_projection := IsStarProjection.zero D
  right_projection := IsStarProjection.zero D
  orthogonal := mul_zero 0

end OrthogonalProjectionPair

structure PackingBounds (ι : A →⋆ₐ[ℂ] D) (Q : OrthogonalProjectionPair D)
    (K : Finset (unitary A)) (η : ℝ) (n : ℕ) : Prop where
  energy : ∀ x ∈ K, ∀ τ : Pureness.TracialState D, Q.energy τ (ι (x : A)) ≤ packingEnergy η n
  remaining : ∀ τ : Pureness.TracialState D, Q.remaining τ ≤ packingRemainder η n
  balance : ∀ x ∈ K, ∀ τ : Pureness.TracialState D, Q.balance τ (ι (x : A)) ≤ packingBalance η n

theorem finite_packing_from_diagonals (ι : A →⋆ₐ[ℂ] D) (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : Pureness.TracialState D, (τ.functional g).re) < δ)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (diagonals : ∀ K : Finset (unitary A), Nonempty (PositiveDiagonal A K (η ^ 2)))
    (n : ℕ) (K : Finset (unitary A)) :
    ∃ Q : OrthogonalProjectionPair D, PackingBounds ι Q K η n := by
  classical
  induction n generalizing K with
  | zero =>
    refine ⟨.zero, ?_⟩
    constructor
    · intro x _ τ
      simp [OrthogonalProjectionPair.zero, OrthogonalProjectionPair.energy]
    · intro τ
      simp [OrthogonalProjectionPair.zero, OrthogonalProjectionPair.remaining,
        OrthogonalProjectionPair.total, τ.normalized]
    · intro x _ τ
      simp [OrthogonalProjectionPair.zero, OrthogonalProjectionPair.balance]
  | succ n ih =>
    let C := Classical.choice (diagonals K)
    obtain ⟨L, hL⟩ := relative_coefficient_tests ι C.coefficient C.contractive
    obtain ⟨Q, hQ⟩ := ih (K ∪ L)
    let KD : Finset (unitary D) := K.image (mapUnitary ι)
    let v : Fin C.size → D := fun i => ι (C.coefficient i)
    have hv (i : Fin C.size) : ‖v i‖ ≤ 1 :=
      (NonUnitalStarAlgHom.norm_apply_le ι _).trans (C.contractive i)
    have hr := Q.total_projection.one_sub
    have hcentral (r : D) (hr : IsStarProjection r) (x : unitary D) (hx : x ∈ KD)
        (τ : Pureness.TracialState D) :
        traceOneNorm τ (weightedAverage C.weight v r - (x : D) *
          weightedAverage C.weight v r * star (x : D)) ≤ η ^ 2 * (τ.functional r).re := by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact weightedAverage_central τ ι C.weight C.coefficient C.weight_nonneg hr y
        (C.commutator y hy).le
    obtain ⟨F, hcompression, hclose, hblocks⟩ := weighted_family_of_average hRR
      C.weight C.weight_nonneg C.weight_sum v hv KD hη hη1 hcentral hr
    let δ : ℝ := η ^ 2 / (Fintype.card (F.Index × Bool) + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨R⟩ := exists_sampled_packing_round hRR hsmall Q.total_projection F KD hη hη1 hδ hcompression
    have herror : R.totalError ≤ η ^ 2 := by
      dsimp [SampledPackingRound.totalError, δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg η]
    have hE : 0 ≤ packingEnergy η n := packingEnergy_nonneg hη.le n
    have hold (τ : Pureness.TracialState D) :
        (τ.functional (Q.total * weightedAverage C.weight v (1 - Q.total))).re ≤
          4 * packingEnergy η n := by
      apply weightedAverage_overlap_le τ C.weight C.weight_nonneg C.weight_sum v Q.total_projection
      apply hL Q.total τ (packingEnergy η n) hE
      intro x hx
      rw [traceTwoNorm_sub_swap]
      exact (Q.total_energy_le τ (ι (x : A))).trans
        (hQ.energy x (Finset.mem_union_right K hx) τ)
    have hdefect : ‖1 - weightedAverage C.weight v 1‖ < η ^ 2 :=
      (map_average_defect ι C.weight C.coefficient).trans_lt C.defect
    have H : R.Estimates (packingEnergy η n) := R.estimates_of_average Q.total_projection hη hη1 hE
      (weightedAverage_nonneg C.weight v C.weight_nonneg hr.nonneg)
      (weightedAverage_le_one C.weight v C.weight_nonneg C.weight_sum hv hr.nonneg hr.norm_le)
      herror (fun τ => weightedAverage_mass τ C.weight v C.weight_nonneg C.weight_sum hv hr hdefect)
      hclose hblocks hold
    refine ⟨Q.appendRound R, ?_⟩
    constructor
    · intro x hx τ
      rw [packingEnergy_succ]
      apply (Q.appendRound_energy R τ (ι (x : A))).trans
      exact add_le_add (hQ.energy x (Finset.mem_union_left L hx) τ)
        (H.inserted_energy (mapUnitary ι x) (Finset.mem_image_of_mem _ hx) τ)
    · intro τ
      change (τ.functional (1 - (Q.appendRound R).total)).re ≤ _
      rw [Q.appendRound_total R]
      apply (H.remaining τ).trans
      apply le_trans _ (packingRemainder_step hη.le n)
      apply add_le_add
      · exact add_le_add (mul_le_mul_of_nonneg_left (hQ.remaining τ)
          (sub_nonneg.mpr hη1.le)) le_rfl
      · exact mul_le_mul_of_nonneg_left (H.overlap_incr τ) (by norm_num)
    · intro x hx τ
      apply (Q.appendRound_balance R τ (ι (x : A))).trans
      apply le_trans _ (packingBalance_step hη.le n)
      exact add_le_add (hQ.balance x (Finset.mem_union_left L hx) τ)
        (H.balance R hη herror τ (mapUnitary ι x) (Finset.mem_image_of_mem _ hx))

end

section

open Filter Topology

lemma exists_packing_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, ∃ n : ℕ, 0 < η ∧ η < 1 ∧
      Real.sqrt (packingEnergy η n) < ε ∧
      (packingRemainder η n + packingBalance η n) / 2 < ε := by
  have hevent : ∀ᶠ H : ℝ in atTop, Real.exp (-H) < ε :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds hε)
  obtain ⟨H, hH, hdecay⟩ := (eventually_gt_atTop (0 : ℝ) |>.and hevent).exists
  let C : ℝ := Real.exp (1000 * H)
  have hC : 0 < C := Real.exp_pos _
  have ht : Tendsto (fun n : ℕ => H / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat H
  have hb : Tendsto (fun n : ℕ => Real.exp (-H) + 3 * H * (H / (n : ℝ)) +
      3 * (H / (n : ℝ)) * C + H * (7 * (H / (n : ℝ)) +
      2 * Real.sqrt (60 * ((H / (n : ℝ)) * C) + 75 * (H / (n : ℝ)))))
      atTop (𝓝 (Real.exp (-H))) := by
    convert ((tendsto_const_nhds.add (ht.const_mul (3 * H))).add
      ((ht.const_mul 3).mul_const C)).add
      (((ht.const_mul 7).add (((ht.mul_const C).const_mul 60 |>.add (ht.const_mul 75)).sqrt.const_mul 2)).const_mul H) using 1
    simp
  have he : Tendsto (fun n : ℕ => Real.sqrt ((H / (n : ℝ)) * C)) atTop (𝓝 0) := by
    simpa using (ht.mul_const C).sqrt
  have hn1 : ∀ᶠ n : ℕ in atTop, H / (n : ℝ) < 1 := ht.eventually (gt_mem_nhds (by norm_num))
  have hne : ∀ᶠ n : ℕ in atTop, Real.sqrt ((H / (n : ℝ)) * C) < ε :=
    he.eventually (gt_mem_nhds hε)
  have hnb := hb.eventually (gt_mem_nhds (show Real.exp (-H) < 2 * ε by linarith))
  obtain ⟨n, hn, hη1, hE, hRB⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and (hn1.and (hne.and hnb))).exists
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let η : ℝ := H / (n : ℝ)
  have hη : 0 < η := div_pos hH hnpos
  have htime : (n : ℝ) * η = H := by dsimp [η]; field_simp
  have hEb : packingEnergy η n ≤ η * C := by
    simpa only [htime] using packingEnergy_exp_bound hη.le n
  have hRb : packingRemainder η n ≤ Real.exp (-H) + 3 * H * η + 3 * η * C := by
    have hd := packing_decay_exp_bound hη1.le n
    rw [htime] at hd
    dsimp [packingRemainder]
    calc
      _ ≤ Real.exp (-H) + 3 * n * η ^ 2 + 3 * (η * C) := by gcongr
      _ = _ := by rw [← htime]; ring
  have hBb : packingBalance η n ≤ H * (7 * η + 2 * Real.sqrt (60 * (η * C) + 75 * η)) := by
    dsimp [packingBalance]
    calc
      _ ≤ (n : ℝ) * (7 * η ^ 2 + 2 * η * Real.sqrt (60 * (η * C) + 75 * η)) := by gcongr
      _ = _ := by rw [← htime]; ring
  refine ⟨η, n, hη, hη1, (Real.sqrt_le_sqrt hEb).trans_lt hE, ?_⟩
  have hsum := add_le_add hRb hBb
  change _ < 2 * ε at hRB
  linarith

end

section

open scoped ComplexOrder

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [CStarAlgebra D]

variable [PartialOrder D] [StarOrderedRing D]

lemma OrthogonalProjectionPair.halving_le (Q : OrthogonalProjectionPair D)
    (τ : Pureness.TracialState D) (x : unitary D) :
    ‖τ.functional (Q.left * (x : D)) - (1 / 2 : ℂ) * τ.functional (x : D)‖ ≤
      (Q.remaining τ + Q.balance τ (x : D)) / 2 := by
  have hid : τ.functional (Q.left * (x : D)) - (1 / 2 : ℂ) * τ.functional (x : D) =
      (1 / 2 : ℂ) * ((τ.functional (Q.left * (x : D)) - τ.functional (Q.right * (x : D))) -
        τ.functional ((1 - Q.total) * (x : D))) := by
    simp only [total, sub_mul, one_mul, add_mul, map_sub, map_add]
    ring
  have hxu : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.one D).norm_le
  have hr := trace_norm_projection_mul_le τ Q.total_projection.one_sub (x : D)
  have hrem : 0 ≤ Q.remaining τ := Complex.nonneg_iff.mp
    (τ.functional.map_nonneg Q.total_projection.one_sub.nonneg) |>.1
  have hr' : ‖τ.functional ((1 - Q.total) * (x : D))‖ ≤ Q.remaining τ := by
    apply hr.trans
    exact (mul_le_mul_of_nonneg_right hxu hrem).trans_eq (one_mul _)
  rw [hid, norm_mul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  calc
    _ ≤ (1 / 2 : ℝ) * (Q.balance τ (x : D) + Q.remaining τ) := by
      gcongr
      exact (norm_sub_le _ _).trans (add_le_add le_rfl hr')
    _ = _ := by ring

theorem finite_set_splitting_from_diagonals (ι : A →⋆ₐ[ℂ] D)
    (hRR : RealRankZero D) (hT : Nonempty (Pureness.TracialState D))
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : Pureness.TracialState D, (τ.functional g).re) < δ)
    (diagonals : ∀ (K : Finset (unitary A)) (μ : ℝ), 0 < μ → Nonempty (PositiveDiagonal A K μ))
    (K : Finset (unitary A)) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : D, IsStarProjection P ∧ ∀ x ∈ K,
      uniformTwoNorm (P * ι (x : A) - ι (x : A) * P) < ε ∧
      uniformHalvingError P (ι (x : A)) < ε := by
  classical
  let := hT
  obtain ⟨η, n, hη, hη1, henergy, hbalance⟩ := exists_packing_parameters hε
  obtain ⟨Q, hQ⟩ := finite_packing_from_diagonals ι hRR hsmall hη hη1
    (fun L => diagonals L (η ^ 2) (sq_pos_of_pos hη)) n K
  refine ⟨Q.left, Q.left_projection, ?_⟩
  intro x hx
  constructor
  · apply lt_of_le_of_lt ?_ henergy
    apply ciSup_le
    intro τ
    rw [traceTwoNorm_sub_swap]
    have h := hQ.energy x hx τ
    have hs : traceTwoNorm τ (ι (x : A) * Q.left - Q.left * ι (x : A)) ^ 2 ≤ packingEnergy η n :=
      (le_add_of_nonneg_right (sq_nonneg _)).trans h
    exact (Real.le_sqrt (traceTwoNorm_nonneg τ _) (packingEnergy_nonneg hη.le n)).mpr hs
  · apply lt_of_le_of_lt ?_ hbalance
    apply ciSup_le
    intro τ
    exact (Q.halving_le τ (mapUnitary ι x)).trans
      (div_le_div_of_nonneg_right (add_le_add (hQ.remaining τ) (hQ.balance x hx τ)) (by norm_num))

end

section

open scoped TensorProduct

variable {A : Type uA} [CStarAlgebra A]

abbrev DiagonalTestSpace (A : Type uA) [CStarAlgebra A] (K : Finset (unitary A)) :=
  (({x : unitary A // x ∈ K} → ⨂[ℂ] (_ : Fin 2), A) × A)

def diagonalTestPoint (K : Finset (unitary A)) : DiagonalTestSpace A K := (0, 1)

def diagonalTestAtom (K : Finset (unitary A)) (v : A) : DiagonalTestSpace A K :=
  (fun x => tensorPair ((x.val : A) * v) (star v) - tensorPair v (star v * (x.val : A)),
    v * star v)

def diagonalTestAtoms (K : Finset (unitary A)) : Set (DiagonalTestSpace A K) :=
  diagonalTestAtom K '' {v : A | ‖v‖ ≤ 1}

def DiagonalDualBound (K : Finset (unitary A)) : Prop :=
  ∀ (f : DiagonalTestSpace A K →L[ℝ] ℝ) (c : ℝ),
    (∀ v : A, ‖v‖ ≤ 1 → f (diagonalTestAtom K v) ≤ c) → f (diagonalTestPoint K) ≤ c

lemma diagonalTestPoint_mem_closure (K : Finset (unitary A))
    (h : DiagonalDualBound K) :
    diagonalTestPoint K ∈ closure (convexHull ℝ (diagonalTestAtoms K)) := by
  classical
  by_contra hn
  obtain ⟨f, c, hf, hc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (diagonalTestAtoms K)).closure isClosed_closure hn
  apply (not_le_of_gt hc) (h f c ?_)
  intro v hv
  exact (hf _ (subset_closure (subset_convexHull ℝ _ ⟨v, hv, rfl⟩))).le

lemma diagonalTest_sum {I : Type uI} [Fintype I] (K : Finset (unitary A))
    (w : I → ℝ) (v : I → A) :
    (∑ i, w i • diagonalTestAtom K (v i)) =
      ((fun x => diagonalCommutator w v (x.val : A)), weightedAverage w v 1) := by
  ext
  · simp [diagonalTestAtom, diagonalCommutator, Finset.sum_apply, Prod.fst_sum]
  · simp [diagonalTestAtom, weightedAverage, Prod.snd_sum]

theorem positiveDiagonal_of_dualBound (K : Finset (unitary A))
    (h : DiagonalDualBound K) {μ : ℝ} (hμ : 0 < μ) :
    Nonempty (PositiveDiagonal A K μ) := by
  classical
  have hcl := diagonalTestPoint_mem_closure K h
  obtain ⟨z, hz, hzμ⟩ := Metric.mem_closure_iff.mp hcl μ hμ
  obtain ⟨I, _, w, a, hw, hw1, ha, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hz
  choose v hv hav using ha
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let w' := w ∘ e
  let v' := v ∘ e
  have hsum' : ∑ i, w' i • diagonalTestAtom K (v' i) = z := by
    dsimp [w', v']
    rw [e.sum_comp (fun i => w i • diagonalTestAtom K (v i))]
    simpa only [hav] using hsum
  have hsnd : ‖1 - weightedAverage w' v' 1‖ < μ := by
    have hd := norm_snd_le (diagonalTestPoint K - z)
    have hd' := hd.trans_lt (by simpa only [dist_eq_norm] using hzμ)
    rw [← hsum', diagonalTest_sum] at hd'
    exact hd'
  refine ⟨{ size := Fintype.card I, weight := w', coefficient := v'
            weight_nonneg := fun i => hw (e i)
            weight_sum := ?_
            contractive := fun i => hv (e i)
            defect := hsnd
            commutator := ?_ }⟩
  · exact (e.sum_comp w).trans hw1
  · intro x hx
    have hd := (norm_le_pi_norm ((diagonalTestPoint K - z).1) ⟨x, hx⟩).trans
      (norm_fst_le (diagonalTestPoint K - z))
    have hd' := hd.trans_lt (by simpa only [dist_eq_norm] using hzμ)
    rw [← hsum', diagonalTest_sum] at hd'
    change ‖0 - diagonalCommutator w' v' (x : A)‖ < μ at hd'
    simpa only [zero_sub, norm_neg] using hd'

end

variable {A : Type uA} [CStarAlgebra A]

theorem diagonal_separation_certificate (K : Finset (unitary A))
    {μ : ℝ} (hμ : 0 < μ) (hno : IsEmpty (PositiveDiagonal A K μ)) :
    ∃ (f : DiagonalTestSpace A K →L[ℝ] ℝ) (c : ℝ),
      (∀ v : A, ‖v‖ ≤ 1 → f (diagonalTestAtom K v) ≤ c) ∧
      c < f (diagonalTestPoint K) := by
  classical
  have hn : ¬ DiagonalDualBound K := fun h =>
    (positiveDiagonal_of_dualBound K h hμ).elim (fun d => isEmptyElim d)
  simp only [DiagonalDualBound, not_forall, not_le] at hn
  obtain ⟨f, c, hf, hc⟩ := hn
  exact ⟨f, c, hf, hc⟩

end CurrentMain

end

end OAI
