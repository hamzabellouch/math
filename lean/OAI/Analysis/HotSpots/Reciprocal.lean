import OAI.Analysis.HotSpots.Basic

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section SingularLayer



namespace ReciprocalKernel

open Matrix Filter Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι]


def pairing (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ := x ⬝ᵥ A *ᵥ y

lemma pairing_symm {A : Matrix ι ι ℝ} (hA : A.IsSymm) (x y : ι → ℝ) :
    pairing A x y = pairing A y x := by
  simpa only [pairing, hA.eq] using Matrix.dotProduct_transpose_mulVec A x y

lemma pairing_sub_smul (A : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ) :
    pairing A (y - t • x) (y - t • x) =
      pairing A y y - t * pairing A y x - t * pairing A x y + t ^ 2 * pairing A x x := by
  simp only [pairing, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct,
    dotProduct_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma pairing_sub_smul_right (A : Matrix ι ι ℝ) (x y z : ι → ℝ) (t : ℝ) :
    pairing A x (y - t • z) = pairing A x y - t * pairing A x z := by
  simp only [pairing, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]

lemma pairing_add_smul_right (A : Matrix ι ι ℝ) (x y z : ι → ℝ) (t : ℝ) :
    pairing A x (y + t • z) = pairing A x y + t * pairing A x z := by
  simp only [pairing, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul, smul_eq_mul]

lemma pairing_add_smul (A : Matrix ι ι ℝ) (x y : ι → ℝ) (t : ℝ) :
    pairing A (y + t • x) (y + t • x) =
      pairing A y y + t * pairing A y x + t * pairing A x y + t ^ 2 * pairing A x x := by
  simp only [pairing, Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
    dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

lemma pairing_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) (x y : ι → ℝ) :
    Tendsto (fun n => pairing (A n) x y) atTop (𝓝 (pairing B x y)) := by
  unfold pairing dotProduct Matrix.mulVec
  exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
    (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))



def OnePositiveSquare (A : Matrix ι ι ℝ) : Prop :=
  A.IsSymm ∧ ∀ x y : ι → ℝ, 0 < pairing A x x → pairing A x y = 0 → pairing A y y ≤ 0


lemma onePositiveSquare_reverse_cauchy {A : Matrix ι ι ℝ} (hA : OnePositiveSquare A)
    (x y : ι → ℝ) (hx : 0 < pairing A x x) :
    pairing A x x * pairing A y y ≤ (pairing A x y) ^ 2 := by
  have hz : pairing A x (y - (pairing A x y / pairing A x x) • x) = 0 := by
    rw [pairing_sub_smul_right]
    field_simp
    ring
  have hn := hA.2 x _ hx hz
  rw [pairing_sub_smul, pairing_symm hA.1 y x] at hn
  have he : pairing A y y - (pairing A x y / pairing A x x) * pairing A x y -
      (pairing A x y / pairing A x x) * pairing A x y +
      (pairing A x y / pairing A x x) ^ 2 * pairing A x x =
      pairing A y y - (pairing A x y) ^ 2 / pairing A x x := by
    field_simp
    ring
  rw [he] at hn
  have := (le_div_iff₀ hx).mp (sub_nonpos.mp hn)
  nlinarith

lemma onePositiveSquare_of_entrywise_tendsto {A : ℕ → Matrix ι ι ℝ}
    {B : Matrix ι ι ℝ} (hA : ∀ n, OnePositiveSquare (A n))
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) :
    OnePositiveSquare B := by
  refine ⟨?_, ?_⟩
  · ext i j
    exact tendsto_nhds_unique (hlim j i)
      ((hlim i j).congr fun n => (hA n).1.apply i j |>.symm)
  · intro x y hx hxy
    have hxx := pairing_tendsto hlim x x
    have hyy := pairing_tendsto hlim y y
    have hxy' := pairing_tendsto hlim x y
    have hp : ∀ᶠ n in atTop, 0 < pairing (A n) x x :=
      hxx.eventually_const_lt hx
    have hn : pairing B x x * pairing B y y - (pairing B x y) ^ 2 ≤ 0 := by
      apply le_of_tendsto ((hxx.mul hyy).sub (hxy'.pow 2))
      filter_upwards [hp] with n hn
      exact sub_nonpos.mpr (onePositiveSquare_reverse_cauchy (hA n) x y hn)
    rw [hxy] at hn
    nlinarith



lemma onePositiveSquare_isotropic_hyperplane {A : Matrix ι ι ℝ}
    (hA : OnePositiveSquare A) (z : ι → ℝ) (hz : pairing A z z = 0)
    (hnonradical : ∃ y, pairing A z y ≠ 0) :
    ∀ x, pairing A z x = 0 → pairing A x x ≤ 0 := by
  intro x hzx
  by_contra hx
  have hx : 0 < pairing A x x := lt_of_not_ge hx
  obtain ⟨y, hy⟩ := hnonradical
  have hxz : pairing A x z = 0 := (pairing_symm hA.1 x z).trans hzx
  let t := ((pairing A x y) ^ 2 / pairing A x x - pairing A y y + 1) /
    (2 * pairing A z y)
  have hn := onePositiveSquare_reverse_cauchy hA x (y + t • z) hx
  rw [pairing_add_smul, pairing_add_smul_right, hz, hxz,
    pairing_symm hA.1 y z] at hn
  dsimp [t] at hn
  have he : pairing A y y +
      (((pairing A x y) ^ 2 / pairing A x x - pairing A y y + 1) /
        (2 * pairing A z y)) * pairing A z y +
      (((pairing A x y) ^ 2 / pairing A x x - pairing A y y + 1) /
        (2 * pairing A z y)) * pairing A z y =
      (pairing A x y) ^ 2 / pairing A x x + 1 := by
    field_simp
    ring
  simp only [mul_zero, add_zero] at hn
  rw [he] at hn
  have he' : pairing A x x * ((pairing A x y) ^ 2 / pairing A x x + 1) =
      (pairing A x y) ^ 2 + pairing A x x := by
    field_simp
  rw [he'] at hn
  linarith

lemma onePositiveSquare_of_nonpos_on_kernel {A : Matrix ι ι ℝ}
    (hA : A.IsSymm) (l : ι → ℝ)
    (h : ∀ x : ι → ℝ, l ⬝ᵥ x = 0 → pairing A x x ≤ 0) :
    OnePositiveSquare A := by
  refine ⟨hA, ?_⟩
  intro x y hx hxy
  have hlx : l ⬝ᵥ x ≠ 0 := by
    intro he
    exact (not_le_of_gt hx) (h x he)
  have hyx : pairing A y x = 0 := (pairing_symm hA y x).trans hxy
  have hz : l ⬝ᵥ (y - ((l ⬝ᵥ y) / (l ⬝ᵥ x)) • x) = 0 := by
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    field_simp
    ring
  have hh := h _ hz
  rw [pairing_sub_smul, hxy, hyx] at hh
  nlinarith [sq_nonneg ((l ⬝ᵥ y) / (l ⬝ᵥ x))]

lemma onePositiveSquare_rankOne_sub_psd (l : ι → ℝ) {U : Matrix ι ι ℝ}
    (hU : U.PosSemidef) :
    OnePositiveSquare (Matrix.vecMulVec l l - U) := by
  apply onePositiveSquare_of_nonpos_on_kernel (l := l)
  · apply Matrix.isHermitian_iff_isSymm.mp
    exact (Matrix.posSemidef_vecMulVec_self_star l |>.isHermitian).sub hU.isHermitian
  · intro x hx
    have hnon := hU.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hnon
    simp [pairing, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, hx, hnon]

lemma pairing_const (a : ℝ) (x y : ι → ℝ) :
    pairing (Matrix.of (fun _ _ => a)) x y = a * (∑ i, x i) * (∑ j, y j) := by
  simp only [pairing, Matrix.mulVec, dotProduct, Matrix.of_apply]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma pairing_scale (A : Matrix ι ι ℝ) (l x y : ι → ℝ) :
    pairing (Matrix.of (fun i j => l i * A i j * l j)) x y =
      pairing A (l * x) (l * y) := by
  simp only [pairing, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.mul_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma onePositiveSquare_scale {A : Matrix ι ι ℝ} (hA : OnePositiveSquare A)
    (l : ι → ℝ) :
    OnePositiveSquare (Matrix.of (fun i j => l i * A i j * l j)) := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [hA.1.apply]
    ring
  · intro x y hx hxy
    rw [pairing_scale] at hx hxy ⊢
    exact hA.2 _ _ hx hxy

lemma onePositiveSquare_const_sub_psd (a : ℝ) {U : Matrix ι ι ℝ}
    (hU : U.PosSemidef) :
    OnePositiveSquare (Matrix.of (fun _ _ => a) - U) := by
  apply onePositiveSquare_of_nonpos_on_kernel (l := fun _ => 1)
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.of_apply]
    have hij : U j i = U i j := by simpa using hU.isHermitian.apply i j
    rw [hij]
  · intro x hx
    have hsum : ∑ i, x i = 0 := by simpa [dotProduct] using hx
    have hn := hU.dotProduct_mulVec_nonneg x
    simp only [star_trivial] at hn
    change pairing (Matrix.of (fun _ _ => a) - U) x x ≤ 0
    change x ⬝ᵥ (Matrix.of (fun _ _ => a) - U) *ᵥ x ≤ 0
    rw [Matrix.sub_mulVec, dotProduct_sub]
    change pairing (Matrix.of (fun _ _ => a)) x x - pairing U x x ≤ 0
    rw [pairing_const, hsum]
    simpa only [pairing, mul_zero, zero_sub, neg_nonpos] using hn



lemma normalized_complement_posSemidef {H : Matrix ι ι ℝ}
    (hH : OnePositiveSquare H) (z : ι) {a : ℝ} (ha : 0 < a)
    (hrow : ∀ j, H z j = a) :
    (Matrix.of (fun _ _ => a) - H).PosSemidef := by
  classical
  have hpair (v : ι → ℝ) : pairing H (Pi.single z 1) v = a * ∑ i, v i := by
    unfold pairing
    rw [single_dotProduct, one_mul]
    change (∑ j, H z j * v j) = a * ∑ i, v i
    simp only [hrow, Finset.mul_sum]
  have he : pairing H (Pi.single z 1) (Pi.single z 1) = a := by
    simp [hpair]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.ext
    intro i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.of_apply]
    rw [hH.1.apply]
  · intro v
    have hz : pairing H (Pi.single z 1) (v - (∑ i, v i) • Pi.single z 1) = 0 := by
      rw [hpair]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      simp
    have hyn := hH.2 (Pi.single z 1) _ (he ▸ ha) hz
    rw [pairing_sub_smul, he, hpair, pairing_symm hH.1 v (Pi.single z 1), hpair] at hyn
    have heval : star v ⬝ᵥ (Matrix.of (fun _ _ => a) - H) *ᵥ v =
        a * (∑ i, v i) ^ 2 - pairing H v v := by
      simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
      change pairing (Matrix.of (fun _ _ => a)) v v - pairing H v v = _
      rw [pairing_const]
      ring
    rw [heval]
    nlinarith

omit [Fintype ι] in

lemma posSemidef_entry_sq_le {U : Matrix ι ι ℝ} (hU : U.PosSemidef) (i j : ι) :
    (U i j) ^ 2 ≤ U i i * U j j := by
  have h := (hU.submatrix ![i, j]).det_nonneg
  simp only [Matrix.det_fin_two, Matrix.submatrix_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] at h
  have hij : U j i = U i j := by simpa using hU.isHermitian.apply i j
  rw [hij] at h
  nlinarith

omit [Fintype ι] in
lemma posSemidef_abs_entry_lt {U : Matrix ι ι ℝ} (hU : U.PosSemidef)
    {a : ℝ} (ha : 0 < a) (hdiag : ∀ i, U i i < a) (i j : ι) : |U i j| < a := by
  have hp : U i i * U j j < a * a := calc
    U i i * U j j ≤ U i i * a :=
      mul_le_mul_of_nonneg_left (hdiag j).le hU.diag_nonneg
    _ < a * a := mul_lt_mul_of_pos_right (hdiag i) ha
  have hs := posSemidef_entry_sq_le hU i j
  nlinarith [sq_abs (U i j), abs_nonneg (U i j)]


lemma posSemidef_entry_pow {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (n : ℕ) :
    (Matrix.of (fun i j => A i j ^ n)).PosSemidef := by
  induction n with
  | zero =>
    simpa [Matrix.vecMulVec] using
      (Matrix.posSemidef_vecMulVec_self_star (fun _ : ι => (1 : ℝ)))
  | succ n ih =>
    have he : Matrix.of (fun i j => A i j ^ (n + 1)) =
        Matrix.of (fun i j => A i j ^ n) ⊙ A := by
      ext i j
      simp [pow_succ]
    rw [he]
    exact ih.hadamard hA


lemma posSemidef_of_entrywise_tendsto {A : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : ∀ i j, Tendsto (fun n => A n i j) atTop (𝓝 (B i j))) : B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    ext i j
    exact tendsto_nhds_unique (hlim j i)
      ((hlim i j).congr fun n => by simpa using (hA n).isHermitian.apply j i)
  · intro x
    have hlimq : Tendsto (fun n => star x ⬝ᵥ A n *ᵥ x) atTop
        (𝓝 (star x ⬝ᵥ B *ᵥ x)) := by
      unfold dotProduct Matrix.mulVec
      exact tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul tendsto_const_nhds))
    exact ge_of_tendsto hlimq (Filter.Eventually.of_forall fun n =>
      (hA n).dotProduct_mulVec_nonneg x)


lemma posSemidef_entry_resolvent {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hsmall : ∀ i j, |A i j| < 1) :
    (Matrix.of (fun i j => A i j / (1 - A i j))).PosSemidef := by
  apply posSemidef_of_entrywise_tendsto
    (A := fun n => ∑ k ∈ Finset.range n, Matrix.of (fun i j => A i j ^ (k + 1)))
  · intro n
    exact Matrix.posSemidef_sum _ (fun k _ => posSemidef_entry_pow hA (k + 1))
  · intro i j
    have hs := (hasSum_geometric_of_norm_lt_one (show ‖A i j‖ < 1 by
      simpa only [Real.norm_eq_abs] using hsmall i j)).mul_left (A i j)
    simpa only [Matrix.sum_apply, Matrix.of_apply, div_eq_mul_inv, pow_succ, mul_comm]
      using hs.tendsto_sum_nat


lemma onePositiveSquare_normalized_update {H : Matrix ι ι ℝ}
    (hH : OnePositiveSquare H) (hpos : ∀ i j, 0 < H i j)
    (z : ι) {a : ℝ} (hrow : ∀ j, H z j = a) {c : ℝ} (hc : 0 ≤ c) :
    OnePositiveSquare (Matrix.of (fun i j => H i j / (1 + c * H i j))) := by
  rcases hc.eq_or_lt with hc | hc
  · subst c
    have he : Matrix.of (fun i j => H i j / (1 + 0 * H i j)) = H := by
      ext i j
      simp
    rwa [he]
  have ha : 0 < a := hrow z ▸ hpos z z
  let U := Matrix.of (fun _ _ => a) - H
  have hU : U.PosSemidef := normalized_complement_posSemidef hH z ha hrow
  have hdiag : ∀ i, U i i < a := by
    intro i
    change a - H i i < a
    exact sub_lt_self _ (hpos i i)
  have hUa : ∀ i j, |U i j| < a := posSemidef_abs_entry_lt hU ha hdiag
  have hd : 0 < 1 + c * a := by positivity
  let r := c / (1 + c * a)
  have hr : 0 < r := div_pos hc hd
  let V := r • U
  have hV : V.PosSemidef := hU.smul hr.le
  have hra : r * a < 1 := by
    dsimp [r]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    linarith
  have hsmall : ∀ i j, |V i j| < 1 := by
    intro i j
    change |r * U i j| < 1
    rw [abs_mul, abs_of_pos hr]
    exact (mul_lt_mul_of_pos_left (hUa i j) hr).trans hra
  have hW := (posSemidef_entry_resolvent hV hsmall).smul
    (show 0 ≤ (1 / (c * (1 + c * a)) : ℝ) by positivity)
  have hP := onePositiveSquare_const_sub_psd (a / (1 + c * a)) hW
  have he : Matrix.of (fun i j => H i j / (1 + c * H i j)) =
      Matrix.of (fun _ _ => a / (1 + c * a)) -
        (1 / (c * (1 + c * a))) • Matrix.of (fun i j => V i j / (1 - V i j)) := by
    ext i j
    have hij := hpos i j
    have hden : 0 < 1 + c * H i j := by positivity
    have hone : 1 - V i j ≠ 0 := ne_of_gt (sub_pos.mpr (abs_lt.mp (hsmall i j)).2)
    simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp [V, U, r] at hone ⊢
    field_simp [ne_of_gt hden, ne_of_gt hd, ne_of_gt hc]
    ring_nf
    field_simp [show 1 + H i j * c ≠ 0 by nlinarith [hden]]
    ring
  rw [he]
  exact hP



theorem reciprocal_rankOne_update {M : Matrix ι ι ℝ} (hM : M.IsSymm)
    (hpos : ∀ i j, 0 < M i j)
    (hrec : OnePositiveSquare (Matrix.of (fun i j => (M i j)⁻¹)))
    (z : ι) {c : ℝ} (hc : 0 ≤ c) :
    OnePositiveSquare (Matrix.of (fun i j => (M i j + c * M i z * M z j)⁻¹)) := by
  let H := Matrix.of (fun i j => M i z * (M i j)⁻¹ * M j z)
  have hH : OnePositiveSquare H := onePositiveSquare_scale hrec (fun i => M i z)
  have hHp : ∀ i j, 0 < H i j := by
    intro i j
    change 0 < M i z * (M i j)⁻¹ * M j z
    exact mul_pos (mul_pos (hpos i z) (inv_pos.mpr (hpos i j))) (hpos j z)
  have hrow : ∀ j, H z j = M z z := by
    intro j
    change M z z * (M z j)⁻¹ * M j z = M z z
    rw [hM.apply j z]
    field_simp [ne_of_gt (hpos j z)]
  have hnew := onePositiveSquare_normalized_update hH hHp z hrow hc
  have hscaled := onePositiveSquare_scale hnew (fun i => (M i z)⁻¹)
  have he : Matrix.of (fun i j => (M i j + c * M i z * M z j)⁻¹) =
      Matrix.of (fun i j => (M i z)⁻¹ * (H i j / (1 + c * H i j)) * (M j z)⁻¹) := by
    ext i j
    have hij := hpos i j
    have hiz := hpos i z
    have hjz := hpos j z
    have hn : 0 < M i j + c * M i z * M j z := by positivity
    simp only [Matrix.of_apply]
    dsimp [H]
    rw [hM.apply z j]
    have hzj := hpos z j
    have hn' : 0 < M i j + c * M i z * M z j := by positivity
    field_simp [ne_of_gt hzj, ne_of_gt hn']
  rw [he]
  exact hscaled


def bordered (B : Matrix ι ι ℝ) (l : ι → ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks B (Matrix.of (fun i _ => l i)) (Matrix.of (fun _ j => l j)) 0

lemma pairing_bordered (B : Matrix ι ι ℝ) (l x y : ι → ℝ) (a b : ℝ) :
    pairing (bordered B l) (Sum.elim x (fun _ => a)) (Sum.elim y (fun _ => b)) =
      pairing B x y + b * (l ⬝ᵥ x) + a * (l ⬝ᵥ y) := by
  simp only [pairing, bordered, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.zero_apply,
    Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, zero_mul,
    mul_add, Finset.sum_add_distrib]
  ring_nf
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma bordered_nonpos_on_kernel {B : Matrix ι ι ℝ} {l : ι → ℝ}
    (hB : OnePositiveSquare (bordered B l)) (hl : l ≠ 0) :
    ∀ x, l ⬝ᵥ x = 0 → pairing B x x ≤ 0 := by
  classical
  have hz : pairing (bordered B l) (Sum.elim 0 (fun _ => 1))
      (Sum.elim 0 (fun _ => 1)) = 0 := by
    rw [pairing_bordered]
    simp [pairing]
  have hrad : ∃ y, pairing (bordered B l) (Sum.elim 0 (fun _ => 1)) y ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hl
    refine ⟨Sum.elim (Pi.single i 1) (fun _ => 0), ?_⟩
    rw [pairing_bordered]
    simpa [pairing] using hi
  have hn := onePositiveSquare_isotropic_hyperplane hB _ hz hrad
  intro x hx
  have horth : pairing (bordered B l) (Sum.elim 0 (fun _ => 1))
      (Sum.elim x (fun _ => 0)) = 0 := by
    rw [pairing_bordered]
    simp [pairing, hx]
  have hh := hn _ horth
  simpa [pairing_bordered] using hh


def ConditionallyNegative (D : Matrix ι ι ℝ) : Prop :=
  D.IsSymm ∧ ∀ x : ι → ℝ, (∑ i, x i) = 0 → pairing D x x ≤ 0


theorem conditionalNegative_scaled_of_bordered {B : Matrix ι ι ℝ} (k : ι → ℝ)
    (hk : ∀ i, k i ≠ 0)
    (hB : OnePositiveSquare (bordered B (fun i => (k i)⁻¹))) :
    ConditionallyNegative (Matrix.of (fun i j => k i * B i j * k j)) := by
  have hsym : B.IsSymm := by
    ext i j
    exact hB.1.apply (Sum.inl i) (Sum.inl j)
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [hsym.apply]
    ring
  · intro x hx
    rw [pairing_scale]
    by_cases hi : IsEmpty ι
    · simp [pairing, dotProduct]
    · have : Nonempty ι := not_isEmpty_iff.mp hi
      have hl : (fun i => (k i)⁻¹) ≠ 0 := by
        intro he
        obtain ⟨i⟩ := ‹Nonempty ι›
        have := congrFun he i
        exact (inv_ne_zero (hk i)) this
      apply bordered_nonpos_on_kernel hB hl
      simpa [dotProduct, hk] using hx

end ReciprocalKernel

namespace ReciprocalKernel
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def eliminate (M : Matrix ι ι ℝ) (w : ι → ℝ) (z : ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => M i j + (w z / (1 - w z * M z z)) * M i z * M z j

omit [Fintype ι] [DecidableEq ι] in
lemma eliminate_denominator_pos {M : Matrix ι ι ℝ} {w f : ι → ℝ}
    (hM : ∀ i j, 0 < M i j) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 < f i)
    {S : Finset ι} {z : ι} (hz : z ∈ S)
    (hb : ∀ i, ∑ j ∈ S, M i j * w j * f j < f i) :
    0 < 1 - w z * M z z := by
  have hs : M z z * w z * f z ≤ ∑ j ∈ S, M z j * w j * f j :=
    Finset.single_le_sum (f := fun j => M z j * w j * f j)
      (fun i hi => mul_nonneg (mul_nonneg (hM z i).le (hw i)) (hf i).le) hz
  have hh := lt_of_le_of_lt hs (hb z)
  nlinarith [hf z]

omit [Fintype ι] [DecidableEq ι] in
lemma eliminate_symm {M : Matrix ι ι ℝ} (hM : M.IsSymm) (w : ι → ℝ) (z : ι) :
    (eliminate M w z).IsSymm := by
  ext i j
  simp only [eliminate, Matrix.transpose_apply, Matrix.of_apply]
  rw [hM.apply j i, hM.apply j z, hM.apply z i]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma eliminate_pos {M : Matrix ι ι ℝ} {w : ι → ℝ} {z : ι}
    (hM : ∀ i j, 0 < M i j) (hw : 0 ≤ w z) (hz : 0 < 1 - w z * M z z) :
    ∀ i j, 0 < eliminate M w z i j := by
  intro i j
  dsimp [eliminate]
  exact add_pos_of_pos_of_nonneg (hM i j)
    (mul_nonneg (mul_nonneg (div_nonneg hw hz.le) (hM i z).le) (hM z j).le)

omit [Fintype ι] in
lemma eliminate_bound {M : Matrix ι ι ℝ} {w f : ι → ℝ}
    (hM : ∀ i j, 0 < M i j) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 < f i)
    {S : Finset ι} {z : ι} (hz : z ∉ S)
    (hb : ∀ i, ∑ j ∈ insert z S, M i j * w j * f j < f i) :
    ∀ i, ∑ j ∈ S, eliminate M w z i j * w j * f j < f i := by
  have hd := eliminate_denominator_pos hM hw hf (Finset.mem_insert_self z S) hb
  have hc : 0 ≤ w z / (1 - w z * M z z) := div_nonneg (hw z) hd.le
  have hb' : ∀ i, M i z * w z * f z + ∑ j ∈ S, M i j * w j * f j < f i := by
    simpa only [Finset.sum_insert hz] using hb
  intro i
  have he : (∑ j ∈ S, eliminate M w z i j * w j * f j) =
      (∑ j ∈ S, M i j * w j * f j) +
        (w z / (1 - w z * M z z)) * M i z * (∑ j ∈ S, M z j * w j * f j) := by
    simp only [eliminate, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  have hz' : ∑ j ∈ S, M z j * w j * f j ≤ (1 - w z * M z z) * f z := by
    linarith [hb' z]
  have hmul := mul_le_mul_of_nonneg_left hz' (mul_nonneg hc (hM i z).le)
  have he' : w z / (1 - w z * M z z) * M i z * ((1 - w z * M z z) * f z) =
      M i z * w z * f z := by field_simp
  rw [he'] at hmul
  linarith [hb' i]

omit [DecidableEq ι] in
lemma eliminate_reciprocal {M : Matrix ι ι ℝ} {w : ι → ℝ} {z : ι}
    (hM : M.IsSymm) (hp : ∀ i j, 0 < M i j)
    (hP : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹))
    (hw : 0 ≤ w z) (hd : 0 < 1 - w z * M z z) :
    OnePositiveSquare (Matrix.of fun i j => (eliminate M w z i j)⁻¹) :=
  reciprocal_rankOne_update hM hp hP z (div_nonneg hw hd.le)




theorem finite_resolvent_of_superharmonic {M : Matrix ι ι ℝ} {w f : ι → ℝ}
    (hM : M.IsSymm) (hp : ∀ i j, 0 < M i j)
    (hP : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹))
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 < f i)
    (S : Finset ι) (hb : ∀ i, ∑ j ∈ S, M i j * w j * f j < f i) :
    ∃ R : Matrix ι ι ℝ, R.IsSymm ∧ (∀ i j, 0 < R i j) ∧
      OnePositiveSquare (Matrix.of fun i j => (R i j)⁻¹) ∧
      ∀ i j, R i j = M i j + ∑ k ∈ S, M i k * w k * R k j := by
  induction S using Finset.induction_on generalizing M with
  | empty => exact ⟨M, hM, hp, hP, by simp⟩
  | @insert z S hz ih =>
    have hd := eliminate_denominator_pos hp hw hf (Finset.mem_insert_self z S) hb
    obtain ⟨R, hRs, hRp, hRP, hReq⟩ := ih (eliminate_symm hM w z)
      (eliminate_pos hp (hw z) hd) (eliminate_reciprocal hM hp hP (hw z) hd)
      (eliminate_bound hp hw hf hz hb)
    refine ⟨R, hRs, hRp, hRP, ?_⟩
    have heq (i j) : R i j = M i j + (∑ k ∈ S, M i k * w k * R k j) +
        (w z / (1 - w z * M z z)) * M i z *
          (M z j + ∑ k ∈ S, M z k * w k * R k j) := by
      rw [hReq i j]
      simp only [eliminate, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_add]
      ring_nf
    have hez (j) : (1 - w z * M z z) * R z j =
        M z j + ∑ k ∈ S, M z k * w k * R k j := by
      have hh := heq z j
      field_simp at hh
      nlinarith
    intro i j
    rw [Finset.sum_insert hz, heq i j, ← hez j]
    field_simp
    ring


open scoped Matrix.Norms.L2Operator

lemma matrix_geometric_nonneg {T : Matrix ι ι ℝ}
    (hT : ∀ i j, 0 ≤ T i j) (hn : ‖T‖ < 1) :
    ∀ i j, 0 ≤ (∑' n : ℕ, T ^ n) i j := by
  intro i j
  have hs := summable_geometric_of_norm_lt_one hn
  have ht := ((continuous_id.matrix_elem i j).tendsto (∑' n : ℕ, T ^ n)).comp hs.hasSum
  apply ge_of_tendsto ht
  filter_upwards [] with S
  change 0 ≤ (∑ n ∈ S, T ^ n) i j
  rw [Matrix.sum_apply]
  exact Finset.sum_nonneg fun n _ => Matrix.pow_apply_nonneg hT n i j



lemma exists_superharmonic_of_weighted_norm_lt_one {M : Matrix ι ι ℝ} {w : ι → ℝ}
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 ≤ w i)
    (hn : ‖Matrix.diagonal (fun i => Real.sqrt (w i)) * M *
      Matrix.diagonal (fun i => Real.sqrt (w i))‖ < 1) :
    ∃ f : ι → ℝ, (∀ i, 0 < f i) ∧
      ∀ i, ∑ j, M i j * w j * f j < f i := by
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (w i))
  let N : Matrix ι ι ℝ := M * D
  let T : Matrix ι ι ℝ := D * N
  let B : Matrix ι ι ℝ := ∑' n : ℕ, T ^ n
  let Q : Matrix ι ι ℝ := N * B * D
  have hnorm : ‖T‖ < 1 := by simpa only [T, N, Matrix.mul_assoc] using hn
  have hT : ∀ i j, 0 ≤ T i j := by
    intro i j
    simp only [T, N, D, Matrix.diagonal_mul, Matrix.mul_diagonal]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (hM i j) (Real.sqrt_nonneg _))
  have hB := matrix_geometric_nonneg hT hnorm
  have hQ : ∀ i j, 0 ≤ Q i j := by
    intro i j
    simp only [Q, D, Matrix.mul_diagonal]
    rw [Matrix.mul_apply]
    simp only [N, D, Matrix.mul_diagonal]
    apply mul_nonneg _ (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (mul_nonneg (hM i k) (Real.sqrt_nonneg _)) (hB k j)
  have hB' : (1 : Matrix ι ι ℝ) + T * B = B := by
    have hh := mul_neg_geom_series T hnorm
    change (1 - T) * B = 1 at hh
    rw [sub_mul, one_mul] at hh
    exact (sub_eq_iff_eq_add.mp hh).symm
  have hD : D * D = Matrix.diagonal w := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hw i)
  have hA : (M * Matrix.diagonal w) * (1 + Q) = Q := by
    rw [← hD]
    change (M * (D * D)) * (1 + N * B * D) = N * B * D
    calc
      _ = N * (1 + T * B) * D := by dsimp [N, T]; noncomm_ring
      _ = _ := by rw [hB']
  let f : ι → ℝ := (1 + Q) *ᵥ (fun _ => 1)
  have hf (i) : f i = 1 + ∑ j, Q i j := by
    simp [f, Matrix.add_mulVec, Matrix.mulVec, dotProduct]
  refine ⟨f, ?_, ?_⟩
  · intro i
    rw [hf]
    have : 0 ≤ ∑ j, Q i j := Finset.sum_nonneg fun j _ => hQ i j
    linarith
  · intro i
    have he := congrArg (fun A : Matrix ι ι ℝ => (A *ᵥ (fun _ => 1)) i) hA
    change (((M * Matrix.diagonal w) * (1 + Q)) *ᵥ (fun _ : ι => (1 : ℝ))) i = _ at he
    rw [← Matrix.mulVec_mulVec] at he
    change ((M * Matrix.diagonal w) *ᵥ f) i = _ at he
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal, mul_one] at he
    rw [he, hf]
    linarith


theorem finite_resolvent {M : Matrix ι ι ℝ} {w : ι → ℝ}
    (hM : M.IsSymm) (hp : ∀ i j, 0 < M i j)
    (hP : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹))
    (hw : ∀ i, 0 ≤ w i)
    (hn : ‖Matrix.diagonal (fun i => Real.sqrt (w i)) * M *
      Matrix.diagonal (fun i => Real.sqrt (w i))‖ < 1) :
    ∃ R : Matrix ι ι ℝ, R.IsSymm ∧ (∀ i j, 0 < R i j) ∧
      OnePositiveSquare (Matrix.of fun i j => (R i j)⁻¹) ∧
      R = M + M * Matrix.diagonal w * R := by
  obtain ⟨f, hf, hb⟩ := exists_superharmonic_of_weighted_norm_lt_one
    (fun i j => (hp i j).le) hw hn
  obtain ⟨R, hRs, hRp, hRP, hReq⟩ := finite_resolvent_of_superharmonic hM hp hP hw hf
    Finset.univ (by simpa using hb)
  refine ⟨R, hRs, hRp, hRP, ?_⟩
  ext i j
  change R i j = M i j + ∑ k, (M * Matrix.diagonal w) i k * R k j
  simp only [Matrix.mul_diagonal]
  exact hReq i j



def finiteResolventKernel (M : Matrix ι ι ℝ) (w : ι → ℝ) : Matrix ι ι ℝ :=
  let D := Matrix.diagonal (fun i => Real.sqrt (w i))
  M + M * D * (1 - D * M * D)⁻¹ * D * M

lemma resolvent_eq_finiteResolventKernel {M R : Matrix ι ι ℝ} {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i)
    (hn : ‖Matrix.diagonal (fun i => Real.sqrt (w i)) * M *
      Matrix.diagonal (fun i => Real.sqrt (w i))‖ < 1)
    (hR : R = M + M * Matrix.diagonal w * R) :
    R = finiteResolventKernel M w := by
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (w i))
  let N : Matrix ι ι ℝ := M * D
  let T : Matrix ι ι ℝ := D * N
  let B : Matrix ι ι ℝ := (1 - T)⁻¹
  let U : Matrix ι ι ℝ := 1 + N * B * D
  have hnorm : ‖T‖ < 1 := by simpa only [T, N, Matrix.mul_assoc] using hn
  have hu : IsUnit (1 - T) := isUnit_one_sub_of_norm_lt_one hnorm
  have hBinv : (1 - T) * B = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hD : D * D = Matrix.diagonal w := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hw i)
  have hA : M * Matrix.diagonal w = N * D := by rw [← hD]; exact (Matrix.mul_assoc ..).symm
  have hKU : (1 - N * D) * U = 1 := by
    calc
      _ = 1 + N * ((1 - T) * B - 1) * D := by dsimp [U, T]; noncomm_ring
      _ = 1 := by rw [hBinv, sub_self, mul_zero, zero_mul, add_zero]
  have hUK : U * (1 - N * D) = 1 := mul_eq_one_comm.mp hKU
  have hKR : (1 - N * D) * R = M := by
    rw [sub_mul, one_mul]
    rw [hA] at hR
    exact sub_eq_iff_eq_add.mpr hR
  calc
    R = (U * (1 - N * D)) * R := by rw [hUK, one_mul]
    _ = U * M := by rw [Matrix.mul_assoc, hKR]
    _ = finiteResolventKernel M w := by
      simp only [U, N, B, T, finiteResolventKernel, D]
      noncomm_ring



theorem finite_quadrature_reciprocal {M : Matrix ι ι ℝ} {w : ι → ℝ}
    (hM : M.IsSymm) (hp : ∀ i j, 0 < M i j)
    (hP : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹))
    (hw : ∀ i, 0 ≤ w i)
    (hn : ‖Matrix.diagonal (fun i => Real.sqrt (w i)) * M *
      Matrix.diagonal (fun i => Real.sqrt (w i))‖ < 1) :
    (∀ i j, 0 < finiteResolventKernel M w i j) ∧
      OnePositiveSquare (Matrix.of fun i j => (finiteResolventKernel M w i j)⁻¹) := by
  obtain ⟨R, _, hpos, hrec, hReq⟩ := finite_resolvent hM hp hP hw hn
  rw [resolvent_eq_finiteResolventKernel hw hn hReq] at hpos hrec
  exact ⟨hpos, hrec⟩

end ReciprocalKernel






open Filter
open scoped Topology
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def resolvent (A : E →L[ℝ] E) : E →L[ℝ] E := ∑' n : ℕ, A ^ n

lemma resolvent_left (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    (1 - A) * resolvent A = 1 := mul_neg_geom_series A hA

lemma resolvent_right (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    resolvent A * (1 - A) = 1 := geom_series_mul_neg A hA

omit [CompleteSpace E] in
lemma resolvent_norm_le (A : E →L[ℝ] E) {d : ℝ} (hA : ‖A‖ ≤ d) (hd : d < 1) :
    ‖resolvent A‖ ≤ (1 - d)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one A (hA.trans_lt hd)
  have h1 : ‖(1 : E →L[ℝ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hi : (1 - ‖A‖)⁻¹ ≤ (1 - d)⁻¹ := by
    apply inv_anti₀ (sub_pos.mpr hd)
    linarith
  dsimp only [resolvent]
  linarith

lemma resolvent_identity (A B : E →L[ℝ] E) (hA : ‖A‖ < 1) (hB : ‖B‖ < 1) :
    resolvent B - resolvent A = resolvent B * (B - A) * resolvent A := by
  have ht : B - A = (1 - A) - (1 - B) := by abel
  rw [ht, mul_sub, sub_mul, mul_assoc, resolvent_left A hA,
    resolvent_right B hB, mul_one, one_mul]

lemma resolvent_strong_tendsto (A : E →L[ℝ] E) (Q : ℕ → E →L[ℝ] E)
    {d : ℝ} (hd : d < 1) (hA : ‖A‖ < 1)
    (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v))) (v : E) :
    Tendsto (fun n => resolvent (Q n) v) atTop (𝓝 (resolvent A v)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  have hz : Tendsto (fun n => (1 - d)⁻¹ * ‖(Q n - A) (resolvent A v)‖) atTop (𝓝 0) := by
    have ht := ((hs (resolvent A v)).sub (tendsto_const_nhds (x := A (resolvent A v)))).norm.const_mul (1 - d)⁻¹
    simpa using ht
  apply squeeze_zero_norm' _ hz
  filter_upwards [hQ] with n hn
  have he := congrArg (fun T : E →L[ℝ] E => T v)
    (resolvent_identity A (Q n) hA (hn.trans_lt hd))
  simp only [sub_apply, mul_apply_eq_comp] at he
  rw [he]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (resolvent_norm_le (Q n) hn hd) (norm_nonneg _))

lemma resolvent_solution (A : E →L[ℝ] E) (hA : ‖A‖ < 1) {u f : E}
    (hu : u - A u = f) : u = resolvent A f := by
  have h := congrArg (fun T : E →L[ℝ] E => T u) (resolvent_right A hA)
  simpa only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, hu] using h.symm

lemma resolvent_nonneg [PartialOrder E] [IsOrderedAddMonoid E] [OrderClosedTopology E]
    (A : E →L[ℝ] E) (hA : ‖A‖ < 1)
    (hpos : ∀ v, 0 ≤ v → 0 ≤ A v) {f : E} (hf : 0 ≤ f) :
    0 ≤ resolvent A f := by
  have ht : ∀ n : ℕ, 0 ≤ (A^n) f := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hpos _ ih
  have hs0 : HasSum (fun n : ℕ => A^n) (resolvent A) :=
    (summable_geometric_of_norm_lt_one hA).hasSum
  have hs := (ContinuousLinearMap.apply ℝ E f).hasSum hs0
  change HasSum (fun n : ℕ => (A^n) f) (resolvent A f) at hs
  rw [← hs.tsum_eq]
  exact tsum_nonneg ht

lemma resolvent_ge_self [PartialOrder E] [IsOrderedAddMonoid E] [OrderClosedTopology E]
    (A : E →L[ℝ] E) (hA : ‖A‖ < 1)
    (hpos : ∀ v, 0 ≤ v → 0 ≤ A v) {f : E} (hf : 0 ≤ f) :
    f ≤ resolvent A f := by
  have h := congrArg (fun T : E →L[ℝ] E => T f) (resolvent_left A hA)
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at h
  have hn := hpos _ (resolvent_nonneg A hA hpos hf)
  calc
    f = resolvent A f - A (resolvent A f) := h.symm
    _ ≤ resolvent A f := sub_le_self _ hn

end StrictHotSpots.BanachResolvent







open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal
namespace StrictHotSpots.CompactKernel

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma kernel_integrable (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    Integrable (fun z => f z • C.curry z) ν :=
  (f.continuous.smul C.curry.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)




def kernelOp (C : C(X × X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ z, f z • C.curry z ∂ν
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (kernel_integrable ν C f) (kernel_integrable ν C g)
      map_smul' := by
        intro r f
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul]
        exact integral_smul r _ }
    (ν.real univ * ‖C‖) (by
      intro f
      calc
        ‖∫ z, f z • C.curry z ∂ν‖ ≤ ∫ z, ‖f z • C.curry z‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : X, ‖f‖ * ‖C‖ ∂ν := by
          apply integral_mono (kernel_integrable ν C f).norm (integrable_const _)
          intro z
          dsimp only
          rw [norm_smul]
          apply mul_le_mul (f.norm_coe_le_norm z) _ (norm_nonneg _) (norm_nonneg _)
          exact (ContinuousMap.norm_le _ (norm_nonneg C)).mpr fun x => C.norm_coe_le_norm (z,x)
        _ = ν.real univ * ‖C‖ * ‖f‖ := by simp [integral_const]; ring)

lemma kernelOp_apply (C : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) :
    kernelOp ν C f x = ∫ z, C (z,x) * f z ∂ν := by
  change (∫ z, f z • C.curry z ∂ν) x = _
  rw [ContinuousMap.integral_apply (kernel_integrable ν C f)]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.curry_apply, mul_comm]

lemma kernelOp_nonneg (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {f : C(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ kernelOp ν C f := by
  intro x
  change 0 ≤ kernelOp ν C f x
  rw [kernelOp_apply]
  exact integral_nonneg fun z => mul_nonneg (hC z x) (hf z)



lemma kernelOp_norm_le (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {d : ℝ} (hd : 0 ≤ d) (hrow : ∀ x, ∫ z, C (z,x) ∂ν ≤ d) :
    ‖kernelOp ν C‖ ≤ d := by
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hd (norm_nonneg f))).mpr
  intro x
  rw [kernelOp_apply]
  calc
    ‖∫ z, C (z,x) * f z ∂ν‖ ≤ ∫ z, ‖C (z,x) * f z‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ z, C (z,x) * ‖f‖ ∂ν := by
      apply integral_mono
      · exact ((C.continuous.comp (continuous_id.prodMk continuous_const)).mul f.continuous).norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact ((C.continuous.comp (continuous_id.prodMk continuous_const)).mul continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · intro z
        dsimp only
        rw [norm_mul, Real.norm_of_nonneg (hC z x)]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm z) (hC z x)
    _ = (∫ z, C (z,x) ∂ν) * ‖f‖ := integral_mul_const _ _
    _ ≤ d * ‖f‖ := mul_le_mul_of_nonneg_right (hrow x) (norm_nonneg f)


omit [MetricSpace X] [CompactSpace X] [BorelSpace X] in
lemma integral_comp_simpleFunc {Y : Type*} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (π : SimpleFunc X Y) (F : Y → E) :
    ∫ x, F (π x) ∂ν = ∑ y ∈ π.range, ν.real (π ⁻¹' {y}) • F y := by
  classical
  have he : (fun x => F (π x)) = fun x =>
      ∑ y ∈ π.range, (π ⁻¹' {y}).indicator (fun _ => F y) x := by
    funext x
    simp [Set.indicator_apply, eq_comm]
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro y hy
    exact integral_indicator_const _ (π.measurableSet_fiber y)
  · intro y hy
    exact (integrable_const (F y)).indicator (π.measurableSet_fiber y)


def sampleOp (π : SimpleFunc X X) (C : C(X × X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) • (ContinuousMap.evalCLM ℝ z).smulRight (C.curry z)

omit [BorelSpace X] in
lemma sampleOp_eq_integral (π : SimpleFunc X X) (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    sampleOp ν π C f = ∫ z, f (π z) • C.curry (π z) ∂ν := by
  rw [integral_comp_simpleFunc ν π (fun z => f z • C.curry z)]
  simp [sampleOp, sum_apply]

omit [BorelSpace X] [IsFiniteMeasure ν] in
lemma sampleOp_apply (π : SimpleFunc X X) (C : C(X × X, ℝ)) (f : C(X, ℝ)) (x : X) :
    sampleOp ν π C f x = ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * f z := by
  simp only [sampleOp, sum_apply, smul_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousMap.evalCLM_apply, ContinuousMap.curry_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro z hz
  ring

omit [BorelSpace X] [IsFiniteMeasure ν] in
lemma sampleOp_nonneg (π : SimpleFunc X X) (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {f : C(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ sampleOp ν π C f := by
  intro x
  change 0 ≤ sampleOp ν π C f x
  rw [sampleOp_apply]
  exact Finset.sum_nonneg fun z _ => mul_nonneg
    (mul_nonneg (measureReal_nonneg) (hC z x)) (hf z)

omit [BorelSpace X] [IsFiniteMeasure ν] in
lemma sampleOp_norm_le (π : SimpleFunc X X) (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {d : ℝ} (hd : 0 ≤ d) (hrow : ∀ x, sampleOp ν π C 1 x ≤ d) :
    ‖sampleOp ν π C‖ ≤ d := by
  apply ContinuousLinearMap.opNorm_le_bound _ hd
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hd (norm_nonneg f))).mpr
  intro x
  rw [sampleOp_apply]
  calc
    ‖∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * f z‖ ≤
      ∑ z ∈ π.range, ‖ν.real (π ⁻¹' {z}) * C (z,x) * f z‖ := norm_sum_le _ _
    _ ≤ ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * ‖f‖ := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul, Real.norm_of_nonneg (mul_nonneg measureReal_nonneg (hC z x))]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm z)
        (mul_nonneg measureReal_nonneg (hC z x))
    _ = sampleOp ν π C 1 x * ‖f‖ := by simp [sampleOp_apply, Finset.sum_mul]
    _ ≤ d * ‖f‖ := mul_le_mul_of_nonneg_right (hrow x) (norm_nonneg f)

variable [Nonempty X]



def quantize (n : ℕ) : SimpleFunc X X := SimpleFunc.nearestPt (denseSeq X) n

lemma quantize_tendsto (x : X) : Tendsto (fun n => quantize (X := X) n x) atTop (𝓝 x) :=
  SimpleFunc.tendsto_nearestPt (by rw [(denseRange_denseSeq X).closure_range]; trivial)

lemma integral_quantize_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : C(X, E)) :
    Tendsto (fun n => ∫ z, F (quantize n z) ∂ν) atTop (𝓝 (∫ z, F z ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact ((quantize n).map F).stronglyMeasurable.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun z => F.norm_coe_le_norm (quantize n z)
  · exact Filter.Eventually.of_forall fun z => F.continuous.continuousAt.tendsto.comp
      (quantize_tendsto z)

lemma sampleOp_strong_tendsto (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    Tendsto (fun n => sampleOp ν (quantize n) C f) atTop (𝓝 (kernelOp ν C f)) := by
  simp only [sampleOp_eq_integral]
  exact integral_quantize_tendsto ν ⟨_, f.continuous.smul C.curry.continuous⟩



lemma sampleOp_eventually_norm_le (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 ≤ C (z,x)) {d d' : ℝ} (hd : 0 ≤ d)
    (hdd' : d < d') (hrow : ∀ x, ∫ z, C (z,x) ∂ν ≤ d) :
    ∀ᶠ n in atTop, ‖sampleOp ν (quantize n) C‖ ≤ d' := by
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (sampleOp_strong_tendsto ν C 1)
    (d' - d) (sub_pos.mpr hdd')
  filter_upwards [eventually_ge_atTop N] with n hn
  apply sampleOp_norm_le ν _ C hC (hd.trans hdd'.le)
  intro x
  have hh := (sampleOp ν (quantize n) C 1 - kernelOp ν C 1).norm_coe_le_norm x
  have hk : kernelOp ν C 1 x ≤ d := by simpa [kernelOp_apply] using hrow x
  have hc : sampleOp ν (quantize n) C 1 x - kernelOp ν C 1 x ≤
      ‖sampleOp ν (quantize n) C 1 - kernelOp ν C 1‖ :=
    (le_abs_self _).trans hh
  have he := hN n hn
  rw [dist_eq_norm] at he
  linarith

end StrictHotSpots.CompactKernel

namespace ReciprocalKernel
open Matrix
lemma onePositiveSquare_submatrix_sum_inl {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ} (hA : OnePositiveSquare A) :
    OnePositiveSquare (A.submatrix Sum.inl Sum.inl) := by
  have he (u v : ι → ℝ) : pairing (A.submatrix Sum.inl Sum.inl) u v =
      pairing A (Sum.elim u (fun _ => 0)) (Sum.elim v (fun _ => 0)) := by
    simp [pairing, dotProduct, Matrix.mulVec, Fintype.sum_sum_type]
  refine ⟨?_, ?_⟩
  · ext i j
    exact hA.1.apply _ _
  · intro u v hu huv
    rw [he] at hu huv ⊢
    exact hA.2 _ _ hu huv
end ReciprocalKernel

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]


def resolvedKernel (C : C(X × X, ℝ)) (A : C(X, ℝ) →L[ℝ] C(X, ℝ)) (x y : X) : ℝ :=
  resolvent A (C.curry y) x

omit [BorelSpace X] [IsFiniteMeasure ν] in


lemma sampled_reciprocal (π : SimpleFunc X X) (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 < C (z,x)) (hsym : ∀ x y, C (x,y) = C (y,x))
    (hP : ∀ (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C (s i,s j))⁻¹))
    {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hrow : ∀ x, sampleOp ν π C 1 x ≤ d)
    {ι : Type} [Fintype ι] (s : ι → X) :
    (∀ i j, 0 < resolvedKernel C (sampleOp ν π C) (s i) (s j)) ∧
      OnePositiveSquare (Matrix.of fun i j =>
        (resolvedKernel C (sampleOp ν π C) (s i) (s j))⁻¹) := by
  classical
  let t : ι ⊕ π.range → X := Sum.elim s Subtype.val
  let w : ι ⊕ π.range → ℝ := Sum.elim (fun _ => 0) (fun z => ν.real (π ⁻¹' {z.val}))
  let M : Matrix (ι ⊕ π.range) (ι ⊕ π.range) ℝ := Matrix.of fun i j => C (t j,t i)
  have hM : M.IsSymm := by ext i j; exact hsym _ _
  have hp : ∀ i j, 0 < M i j := fun i j => hC _ _
  have hrec : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹) := by
    have he : (Matrix.of fun i j => (M i j)⁻¹) =
        (Matrix.of fun i j => (C (t i,t j))⁻¹) := by ext i j; simp [M, hsym]
    rw [he]
    exact hP _ t
  have hw : ∀ i, 0 ≤ w i := by intro i; cases i <;> simp [w, measureReal_nonneg]
  have hsum (i : ι ⊕ π.range) (f : C(X, ℝ)) :
      ∑ j, M i j * w j * f (t j) = sampleOp ν π C f (t i) := by
    simp only [Fintype.sum_sum_type, M, w, t, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
      sampleOp_apply]
    rw [Finset.sum_subtype π.range (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hb : ∀ i, ∑ j ∈ Finset.univ, M i j * w j * (1 : ℝ) < 1 := by
    intro i
    have he := hsum i 1
    simp only [ContinuousMap.one_apply] at he
    exact (he ▸ hrow (t i)).trans_lt hd1
  obtain ⟨R,hRs,hRp,hRrec,hReq⟩ := finite_resolvent_of_superharmonic
    hM hp hrec hw (fun _ => one_pos) Finset.univ hb
  have hn : ‖sampleOp ν π C‖ < 1 :=
    (sampleOp_norm_le ν π C (fun z x => (hC z x).le) hd hrow).trans_lt hd1
  have hmatch (j : ι ⊕ π.range) : ∀ i,
      R i j = resolvedKernel C (sampleOp ν π C) (t i) (t j) := by
    let u : C(X, ℝ) := C.curry (t j) +
      ∑ z : π.range, (ν.real (π ⁻¹' {z.val}) * R (Sum.inr z) j) • C.curry z.val
    have hu (i : ι ⊕ π.range) : u (t i) = R i j := by
      rw [hReq i j]
      simp only [u, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.curry_apply, smul_eq_mul,
        Fintype.sum_sum_type, M, w, t, Sum.elim_inl, Sum.elim_inr,
        Matrix.of_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      ring
    have he : u - sampleOp ν π C u = C.curry (t j) := by
      ext x
      simp only [ContinuousMap.sub_apply, sampleOp_apply]
      rw [Finset.sum_subtype π.range (fun _ => Iff.rfl)]
      have hz (z : π.range) : u z.val = R (Sum.inr z) j := hu (Sum.inr z)
      simp only [hz, u, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.curry_apply, smul_eq_mul]
      have hsum' : (∑ z : π.range, (ν.real (π ⁻¹' {↑z}) * R (Sum.inr z) j) * C (↑z,x)) =
          ∑ z : π.range, ν.real (π ⁻¹' {↑z}) * C (↑z,x) * R (Sum.inr z) j := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      rw [hsum']
      abel
    intro i
    rw [← hu i, resolvent_solution _ hn he]
    rfl
  refine ⟨fun i j => ?_, ?_⟩
  · simpa only [t, Sum.elim_inl, hmatch] using hRp (Sum.inl i) (Sum.inl j)
  · have hsub := onePositiveSquare_submatrix_sum_inl hRrec
    convert hsub using 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hmatch, t, Sum.elim_inl]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma continuousMap_orderClosed : OrderClosedTopology C(X, ℝ) := by
  constructor
  have he : {p : C(X, ℝ) × C(X, ℝ) | p.1 ≤ p.2} =
      ⋂ x : X, {p : C(X, ℝ) × C(X, ℝ) | p.1 x ≤ p.2 x} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [he]
  exact isClosed_iInter fun x => isClosed_le
    ((ContinuousMap.evalCLM ℝ x).continuous.comp continuous_fst)
    ((ContinuousMap.evalCLM ℝ x).continuous.comp continuous_snd)

omit [MeasurableSpace X] [BorelSpace X] in
lemma continuous_resolvent_nonneg (A : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hA : ‖A‖ < 1) (hpos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ A f)
    {f : C(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ resolvent A f := by
  let : OrderClosedTopology C(X, ℝ) := continuousMap_orderClosed
  exact resolvent_nonneg A hA hpos hf


omit [MeasurableSpace X] [BorelSpace X] in
lemma resolvedKernel_ge (C : C(X × X, ℝ)) {A : C(X, ℝ) →L[ℝ] C(X, ℝ)}
    (hA : ‖A‖ < 1) (hpos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ A f)
    (hC : ∀ z x, 0 ≤ C (z,x)) (x y : X) :
    C (y,x) ≤ resolvedKernel C A x y := by
  have hp : 0 ≤ C.curry y := fun x => hC y x
  have hn := hpos _ (continuous_resolvent_nonneg A hA hpos hp)
  have he := congrArg (fun T : C(X, ℝ) →L[ℝ] C(X, ℝ) => T (C.curry y))
    (resolvent_left A hA)
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at he
  have hex := congrArg (fun f : C(X, ℝ) => f x) he
  change resolvedKernel C A x y - A (resolvent A (C.curry y)) x = C (y,x) at hex
  have hnx := hn x
  change 0 ≤ A (resolvent A (C.curry y)) x at hnx
  linarith

lemma resolvedKernel_tendsto [Nonempty X] (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 ≤ C (z,x)) {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hrow : ∀ x, ∫ z, C (z,x) ∂ν ≤ d) (x y : X) :
    Tendsto (fun n => resolvedKernel C (sampleOp ν (quantize n) C) x y) atTop
      (𝓝 (resolvedKernel C (kernelOp ν C) x y)) := by
  have hn := kernelOp_norm_le ν C hC hd hrow
  have hh := BanachResolvent.resolvent_strong_tendsto (kernelOp ν C)
    (fun n => sampleOp ν (quantize n) C) (d := (1+d)/2) (by linarith)
    (hn.trans_lt hd1)
    (sampleOp_eventually_norm_le ν C hC hd (by linarith) hrow)
    (sampleOp_strong_tendsto ν C) (C.curry y)
  exact ((ContinuousMap.evalCLM ℝ x).continuous.tendsto _).comp hh




theorem compact_reciprocal_of_row_bound [Nonempty X] (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 < C (z,x)) (hsym : ∀ x y, C (x,y) = C (y,x))
    (hP : ∀ (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C (s i,s j))⁻¹))
    {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hrow : ∀ x, ∫ z, C (z,x) ∂ν ≤ d)
    {ι : Type} [Fintype ι] (s : ι → X) :
    (∀ i j, 0 < resolvedKernel C (kernelOp ν C) (s i) (s j)) ∧
      OnePositiveSquare (Matrix.of fun i j =>
        (resolvedKernel C (kernelOp ν C) (s i) (s j))⁻¹) := by
  have hn := kernelOp_norm_le ν C (fun z x => (hC z x).le) hd hrow
  have hp (x y : X) : 0 < resolvedKernel C (kernelOp ν C) x y :=
    (hC y x).trans_le (resolvedKernel_ge C (hn.trans_lt hd1)
      (fun f hf => kernelOp_nonneg ν C (fun z x => (hC z x).le) hf)
      (fun z x => (hC z x).le) x y)
  refine ⟨fun i j => hp _ _, ?_⟩
  have he := sampleOp_eventually_norm_le ν C (fun z x => (hC z x).le) hd
    (show d < (1+d)/2 by linarith) hrow
  have hr : ∀ᶠ n in atTop, ∀ x, sampleOp ν (quantize n) C 1 x ≤ (1+d)/2 := by
    filter_upwards [he] with n hn x
    calc
      sampleOp ν (quantize n) C 1 x ≤ ‖sampleOp ν (quantize n) C 1 x‖ := le_abs_self _
      _ ≤ ‖sampleOp ν (quantize n) C 1‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖sampleOp ν (quantize n) C‖ * ‖(1 : C(X, ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1+d)/2 := by simpa using hn
  obtain ⟨N,hN⟩ := eventually_atTop.mp hr
  apply onePositiveSquare_of_entrywise_tendsto
    (A := fun n => Matrix.of fun i j =>
      (resolvedKernel C (sampleOp ν (quantize (n+N)) C) (s i) (s j))⁻¹)
  · intro n
    exact (sampled_reciprocal ν (quantize (n+N)) C hC hsym hP
      (show 0 ≤ (1+d)/2 by linarith) (by linarith) (hN _ (Nat.le_add_left _ _)) s).2
  · intro i j
    exact ((resolvedKernel_tendsto ν C (fun z x => (hC z x).le) hd hd1 hrow (s i) (s j)).inv₀
      (hp _ _).ne').comp (tendsto_add_atTop_nat N)

end StrictHotSpots.CompactKernel


namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma integral_norm_L2_le (f : Lp ℝ 2 ν) :
    ∫ z, ‖f z‖ ∂ν ≤ ‖f‖ * ‖ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))‖ := by
  have he : ∫ z, ‖f z‖ ∂ν =
      inner ℝ |f| (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_abs f, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (1 : C(X, ℝ))]
      with z hz h1
    change ‖f z‖ = (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))) z * (|f|) z
    rw [hz, h1]
    simp [Real.norm_eq_abs]
  rw [he]
  simpa only [norm_abs_eq_norm] using real_inner_le_norm |f| (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ)))

lemma l2kernel_integrable (C : C(X × X, ℝ)) (f : Lp ℝ 2 ν) :
    Integrable (fun z => f z • C.curry z) ν := by
  apply ((Lp.memLp f).integrable (by norm_num)).norm.mul_const ‖C‖ |>.mono'
    ((Lp.aestronglyMeasurable f).smul C.curry.continuous.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖f z • C.curry z‖ ≤ _
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (ContinuousMap.norm_le _ (norm_nonneg C)).mpr fun x => C.norm_coe_le_norm (z,x)



def l2SectionOp (C : C(X × X, ℝ)) : Lp ℝ 2 ν →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ z, f z • C.curry z ∂ν
      map_add' := by
        intro f g
        change (∫ z, (f+g) z • C.curry z ∂ν) = _
        calc
          _ = ∫ z, f z • C.curry z + g z • C.curry z ∂ν := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f g] with z hz
            rw [hz, Pi.add_apply, add_smul]
          _ = _ := integral_add (l2kernel_integrable ν C f) (l2kernel_integrable ν C g)
      map_smul' := by
        intro r f
        calc
          _ = ∫ z, r • (f z • C.curry z) ∂ν := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul r f] with z hz
            simp [hz, mul_smul]
          _ = _ := integral_smul r _ }
    (‖C‖ * ‖ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))‖) (by
      intro f
      calc
        ‖∫ z, f z • C.curry z ∂ν‖ ≤ ∫ z, ‖f z • C.curry z‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ ∫ z, ‖f z‖ * ‖C‖ ∂ν := by
          apply integral_mono (l2kernel_integrable ν C f).norm
            (((Lp.memLp f).integrable (by norm_num)).norm.mul_const _)
          intro z
          dsimp only
          rw [norm_smul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact (ContinuousMap.norm_le _ (norm_nonneg C)).mpr fun x => C.norm_coe_le_norm (z,x)
        _ = (∫ z, ‖f z‖ ∂ν) * ‖C‖ := integral_mul_const _ _
        _ ≤ (‖f‖ * ‖ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))‖) * ‖C‖ :=
          mul_le_mul_of_nonneg_right (integral_norm_L2_le ν f) (norm_nonneg _)
        _ = _ := by ring)

lemma l2SectionOp_apply (C : C(X × X, ℝ)) (f : Lp ℝ 2 ν) (x : X) :
    l2SectionOp ν C f x = ∫ z, C (z,x) * f z ∂ν := by
  change (∫ z, f z • C.curry z ∂ν) x = _
  rw [ContinuousMap.integral_apply (l2kernel_integrable ν C f)]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.curry_apply, mul_comm]

lemma l2SectionOp_toLp (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    l2SectionOp ν C (ContinuousMap.toLp 2 ν ℝ f) = kernelOp ν C f := by
  ext x
  rw [kernelOp_apply, l2SectionOp_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν f] with z hz
  rw [hz]

lemma l2SectionOp_nonneg (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {f : Lp ℝ 2 ν} (hf : 0 ≤ f) : 0 ≤ l2SectionOp ν C f := by
  intro x
  change 0 ≤ l2SectionOp ν C f x
  rw [l2SectionOp_apply]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with z hz
  exact mul_nonneg (hC z x) hz

def l2Op (C : C(X × X, ℝ)) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (ContinuousMap.toLp 2 ν ℝ).comp (l2SectionOp ν C)

lemma l2Op_nonneg (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    {f : Lp ℝ 2 ν} (hf : 0 ≤ f) : 0 ≤ l2Op ν C f := by
  apply (Lp.coeFn_nonneg _).mp
  have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (l2SectionOp ν C f)
  filter_upwards [he] with x hx
  exact (l2SectionOp_nonneg ν C hC hf x).trans_eq hx.symm



theorem exists_superharmonic (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (hn : ‖l2Op ν C‖ < 1) :
    ∃ f : C(X, ℝ), (∀ x, 1 ≤ f x) ∧ kernelOp ν C f = f - 1 := by
  let a := ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))
  let g := resolvent (l2Op ν C) a
  let f : C(X, ℝ) := 1 + l2SectionOp ν C g
  have ha : 0 ≤ a := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (1 : C(X, ℝ))] with x hx
    change 0 ≤ (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))) x
    rw [hx]
    exact zero_le_one
  have hg : 0 ≤ g := resolvent_nonneg _ hn (fun v hv => l2Op_nonneg ν C hC hv) ha
  have hf : ContinuousMap.toLp 2 ν ℝ f = g := by
    have he := congrArg (fun T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => T a)
      (resolvent_left (l2Op ν C) hn)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at he
    change g - l2Op ν C g = a at he
    dsimp only [f]
    rw [map_add]
    change a + l2Op ν C g = g
    exact (sub_eq_iff_eq_add.mp he).symm
  refine ⟨f, ?_, ?_⟩
  · intro x
    have hp := l2SectionOp_nonneg ν C hC hg x
    change 0 ≤ l2SectionOp ν C g x at hp
    change 1 ≤ 1 + l2SectionOp ν C g x
    linarith
  · rw [← l2SectionOp_toLp, hf]
    dsimp only [f]
    abel

end StrictHotSpots.CompactKernel


namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

def invMap (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) : C(X, ℝ) :=
  ⟨fun x => (f x)⁻¹, f.continuous.inv₀ (fun x => (hf x).ne')⟩

def scaledKernel (C : C(X × X, ℝ)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) :
    C(X × X, ℝ) :=
  ⟨fun p => C p * f p.1 / f p.2,
    (C.continuous.mul (f.continuous.comp continuous_fst)).div
      (f.continuous.comp continuous_snd) (fun p => (hf p.2).ne')⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma scaledKernel_pos (C : C(X × X, ℝ)) (hC : ∀ z x, 0 < C (z,x))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) (z x : X) :
    0 < scaledKernel C f hf (z,x) := div_pos (mul_pos (hC z x) (hf z)) (hf x)

lemma kernelOp_scaled (C : C(X × X, ℝ)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (u : C(X, ℝ)) :
    kernelOp ν (scaledKernel C f hf) u = invMap f hf * kernelOp ν C (f*u) := by
  ext x
  simp only [kernelOp_apply, ContinuousMap.mul_apply]
  change (∫ z, (C (z,x) * f z / f x) * u z ∂ν) =
    (f x)⁻¹ * ∫ z, C (z,x) * (f z * u z) ∂ν
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by ring

omit [BorelSpace X] [IsFiniteMeasure ν] in
lemma sampleOp_scaled (π : SimpleFunc X X) (C : C(X × X, ℝ))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) (u : C(X, ℝ)) :
    sampleOp ν π (scaledKernel C f hf) u = invMap f hf * sampleOp ν π C (f*u) := by
  ext x
  simp only [sampleOp_apply, ContinuousMap.mul_apply]
  change (∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * (C (z,x) * f z / f x) * u z) =
    (f x)⁻¹ * ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) * C (z,x) * (f z * u z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma mul_invMap (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) : f * invMap f hf = 1 := by
  ext x
  exact mul_inv_cancel₀ (hf x).ne'

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma invMap_mul_cancel (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) (u : C(X, ℝ)) :
    f * (invMap f hf * u) = u := by rw [← mul_assoc, mul_invMap, one_mul]



def rescaledKernel (C : C(X × X, ℝ)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (A : C(X, ℝ) →L[ℝ] C(X, ℝ)) (x y : X) : ℝ :=
  f x * resolvent A (invMap f hf * C.curry y) x

lemma scaled_row_bound [Nonempty X] (C : C(X × X, ℝ))
    (f : C(X, ℝ)) (hf : ∀ x, 1 ≤ f x) (he : kernelOp ν C f = f - 1) :
    0 ≤ 1 - ‖f‖⁻¹ ∧ 1 - ‖f‖⁻¹ < 1 ∧
      ∀ x, ∫ z, scaledKernel C f (fun x => (hf x).trans_lt' zero_lt_one) (z,x) ∂ν
        ≤ 1 - ‖f‖⁻¹ := by
  have hfn : 1 ≤ ‖f‖ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (hf x).trans ((le_abs_self _).trans (f.norm_coe_le_norm x))
  have hfnpos : 0 < ‖f‖ := lt_of_lt_of_le zero_lt_one hfn
  refine ⟨sub_nonneg.mpr (inv_le_one_of_one_le₀ hfn), by linarith [inv_pos.mpr hfnpos], ?_⟩
  intro x
  have hx : 0 < f x := lt_of_lt_of_le zero_lt_one (hf x)
  have hfx : f x ≤ ‖f‖ := (le_abs_self _).trans (f.norm_coe_le_norm x)
  have hxf := inv_anti₀ hx hfx
  have hr := congrArg (fun u : C(X, ℝ) => u x)
    (kernelOp_scaled ν C f (fun x => lt_of_lt_of_le zero_lt_one (hf x)) 1)
  simp only [mul_one, he, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, kernelOp_apply] at hr
  change (∫ z, scaledKernel C f _ (z,x) ∂ν) = (f x)⁻¹ * (f x - 1) at hr
  rw [hr, mul_sub, inv_mul_cancel₀ hx.ne', mul_one]
  linarith

end StrictHotSpots.CompactKernel

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]


def l2ResolvedKernel (C : C(X × X, ℝ)) (x y : X) : ℝ :=
  C (y,x) + l2SectionOp ν C
    (resolvent (l2Op ν C) (ContinuousMap.toLp 2 ν ℝ (C.curry y))) x

omit [MeasurableSpace X] [BorelSpace X] in
lemma scaled_solution (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (A B : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hB : ‖B‖ < 1)
    (hscale : ∀ u, B u = invMap f hf * A (f * u))
    {u v : C(X, ℝ)} (heq : u - A u = v) :
    u = f * resolvent B (invMap f hf * v) := by
  have h : invMap f hf * u - B (invMap f hf * u) = invMap f hf * v := by
    rw [hscale, invMap_mul_cancel, ← mul_sub, heq]
  have hr := congrArg (fun z : C(X, ℝ) => f * z) (resolvent_solution B hB h)
  rwa [invMap_mul_cancel] at hr

lemma rescaledKernel_eq_l2ResolvedKernel (C : C(X × X, ℝ))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (hL : ‖l2Op ν C‖ < 1) (hC : ‖kernelOp ν (scaledKernel C f hf)‖ < 1)
    (x y : X) :
    rescaledKernel C f hf (kernelOp ν (scaledKernel C f hf)) x y =
      l2ResolvedKernel ν C x y := by
  let g := resolvent (l2Op ν C) (ContinuousMap.toLp 2 ν ℝ (C.curry y))
  let u : C(X, ℝ) := C.curry y + l2SectionOp ν C g
  have hg : ContinuousMap.toLp 2 ν ℝ u = g := by
    have he := congrArg (fun T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν =>
      T (ContinuousMap.toLp 2 ν ℝ (C.curry y))) (resolvent_left (l2Op ν C) hL)
    simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at he
    change g - l2Op ν C g = ContinuousMap.toLp 2 ν ℝ (C.curry y) at he
    change ContinuousMap.toLp 2 ν ℝ (C.curry y + l2SectionOp ν C g) = g
    rw [map_add]
    exact (sub_eq_iff_eq_add.mp he).symm
  have hu : u - kernelOp ν C u = C.curry y := by
    rw [← l2SectionOp_toLp, hg]
    dsimp only [u]
    abel
  have hu' := scaled_solution f hf (kernelOp ν C)
    (kernelOp ν (scaledKernel C f hf)) hC (kernelOp_scaled ν C f hf) hu
  have h := congrArg (fun v : C(X, ℝ) => v x) hu'
  exact h.symm

lemma l2ResolvedKernel_ge (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (hn : ‖l2Op ν C‖ < 1) (x y : X) :
    C (y,x) ≤ l2ResolvedKernel ν C x y := by
  have hy : 0 ≤ ContinuousMap.toLp 2 ν ℝ (C.curry y) := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (C.curry y)] with z hz
    rw [hz]
    exact hC y z
  have hp := l2SectionOp_nonneg ν C hC
    (resolvent_nonneg (l2Op ν C) hn (fun v hv => l2Op_nonneg ν C hC hv) hy) x
  exact le_add_of_nonneg_right hp

omit [BorelSpace X] [IsFiniteMeasure ν] in


lemma sampled_rescaled_reciprocal (π : SimpleFunc X X) (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 < C (z,x)) (hsym : ∀ x y, C (x,y) = C (y,x))
    (hP : ∀ (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C (s i,s j))⁻¹))
    (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hrow : ∀ x, sampleOp ν π (scaledKernel C f hf) 1 x ≤ d)
    {ι : Type} [Fintype ι] (s : ι → X) :
    (∀ i j, 0 < rescaledKernel C f hf (sampleOp ν π (scaledKernel C f hf)) (s i) (s j)) ∧
      OnePositiveSquare (Matrix.of fun i j =>
        (rescaledKernel C f hf (sampleOp ν π (scaledKernel C f hf)) (s i) (s j))⁻¹) := by
  classical
  let t : ι ⊕ π.range → X := Sum.elim s Subtype.val
  let w : ι ⊕ π.range → ℝ := Sum.elim (fun _ => 0) (fun z => ν.real (π ⁻¹' {z.val}))
  let M : Matrix (ι ⊕ π.range) (ι ⊕ π.range) ℝ := Matrix.of fun i j => C (t j,t i)
  have hM : M.IsSymm := by ext i j; exact hsym _ _
  have hp : ∀ i j, 0 < M i j := fun i j => hC _ _
  have hrec : OnePositiveSquare (Matrix.of fun i j => (M i j)⁻¹) := by
    have he : (Matrix.of fun i j => (M i j)⁻¹) =
        (Matrix.of fun i j => (C (t i,t j))⁻¹) := by ext i j; simp [M, hsym]
    rw [he]
    exact hP _ t
  have hw : ∀ i, 0 ≤ w i := by intro i; cases i <;> simp [w, measureReal_nonneg]
  have hsum (i : ι ⊕ π.range) (v : C(X, ℝ)) :
      ∑ j, M i j * w j * v (t j) = sampleOp ν π C v (t i) := by
    simp only [Fintype.sum_sum_type, M, w, t, Sum.elim_inl, Sum.elim_inr,
      Matrix.of_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
      sampleOp_apply]
    rw [Finset.sum_subtype π.range (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hb : ∀ i, ∑ j ∈ Finset.univ, M i j * w j * f (t j) < f (t i) := by
    intro i
    rw [hsum]
    have he := congrArg (fun v : C(X, ℝ) => f * v) (sampleOp_scaled ν π C f hf 1)
    rw [mul_one, invMap_mul_cancel] at he
    have hx := congrArg (fun v : C(X, ℝ) => v (t i)) he
    change f (t i) * sampleOp ν π (scaledKernel C f hf) 1 (t i) = sampleOp ν π C f (t i) at hx
    rw [← hx]
    exact (mul_le_mul_of_nonneg_left (hrow (t i)) (hf _).le).trans_lt
      (by simpa using (mul_lt_mul_of_pos_left hd1 (hf (t i))))
  obtain ⟨R,hRs,hRp,hRrec,hReq⟩ := finite_resolvent_of_superharmonic
    hM hp hrec hw (fun i => hf (t i)) Finset.univ hb
  have hn : ‖sampleOp ν π (scaledKernel C f hf)‖ < 1 :=
    (sampleOp_norm_le ν π _ (fun z x => (scaledKernel_pos C hC f hf z x).le) hd hrow).trans_lt hd1
  have hmatch (j : ι ⊕ π.range) : ∀ i,
      R i j = rescaledKernel C f hf (sampleOp ν π (scaledKernel C f hf)) (t i) (t j) := by
    let u : C(X, ℝ) := C.curry (t j) +
      ∑ z : π.range, (ν.real (π ⁻¹' {z.val}) * R (Sum.inr z) j) • C.curry z.val
    have hu (i : ι ⊕ π.range) : u (t i) = R i j := by
      rw [hReq i j]
      simp only [u, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.curry_apply, smul_eq_mul,
        Fintype.sum_sum_type, M, w, t, Sum.elim_inl, Sum.elim_inr,
        Matrix.of_apply, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro z hz
      ring
    have he : u - sampleOp ν π C u = C.curry (t j) := by
      ext x
      simp only [ContinuousMap.sub_apply, sampleOp_apply]
      rw [Finset.sum_subtype π.range (fun _ => Iff.rfl)]
      have hz (z : π.range) : u z.val = R (Sum.inr z) j := hu (Sum.inr z)
      simp only [hz, u, ContinuousMap.add_apply, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, ContinuousMap.curry_apply, smul_eq_mul]
      have hsum' : (∑ z : π.range, (ν.real (π ⁻¹' {↑z}) * R (Sum.inr z) j) * C (↑z,x)) =
          ∑ z : π.range, ν.real (π ⁻¹' {↑z}) * C (↑z,x) * R (Sum.inr z) j := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      rw [hsum']
      abel
    have he' := scaled_solution f hf (sampleOp ν π C)
      (sampleOp ν π (scaledKernel C f hf)) hn (sampleOp_scaled ν π C f hf) he
    intro i
    rw [← hu i, he']
    rfl
  refine ⟨fun i j => ?_, ?_⟩
  · simpa only [t, Sum.elim_inl, hmatch] using hRp (Sum.inl i) (Sum.inl j)
  · have hsub := onePositiveSquare_submatrix_sum_inl hRrec
    convert hsub using 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hmatch, t, Sum.elim_inl]

lemma rescaledKernel_tendsto [Nonempty X] (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 ≤ C (z,x)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    {d : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hrow : ∀ x, ∫ z, scaledKernel C f hf (z,x) ∂ν ≤ d) (x y : X) :
    Tendsto (fun n => rescaledKernel C f hf (sampleOp ν (quantize n) (scaledKernel C f hf)) x y) atTop
      (𝓝 (rescaledKernel C f hf (kernelOp ν (scaledKernel C f hf)) x y)) := by
  have hp (z x : X) : 0 ≤ scaledKernel C f hf (z,x) :=
    div_nonneg (mul_nonneg (hC z x) (hf z).le) (hf x).le
  have hn := kernelOp_norm_le ν (scaledKernel C f hf) hp hd hrow
  have hh := BanachResolvent.resolvent_strong_tendsto (kernelOp ν (scaledKernel C f hf))
    (fun n => sampleOp ν (quantize n) (scaledKernel C f hf))
    (d := (1+d)/2) (by linarith) (hn.trans_lt hd1)
    (sampleOp_eventually_norm_le ν (scaledKernel C f hf) hp hd (by linarith) hrow)
    (sampleOp_strong_tendsto ν (scaledKernel C f hf)) (invMap f hf * C.curry y)
  exact (((ContinuousMap.evalCLM ℝ x).continuous.tendsto _).comp hh).const_mul (f x)

end StrictHotSpots.CompactKernel

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]




theorem compact_reciprocal_of_l2_norm_lt_one [Nonempty X] (C : C(X × X, ℝ))
    (hC : ∀ z x, 0 < C (z,x)) (hsym : ∀ x y, C (x,y) = C (y,x))
    (hP : ∀ (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C (s i,s j))⁻¹))
    (hL : ‖l2Op ν C‖ < 1)
    {ι : Type} [Fintype ι] (s : ι → X) :
    (∀ i j, 0 < l2ResolvedKernel ν C (s i) (s j)) ∧
      OnePositiveSquare (Matrix.of fun i j => (l2ResolvedKernel ν C (s i) (s j))⁻¹) := by
  obtain ⟨f,hf,heq⟩ := exists_superharmonic ν C (fun z x => (hC z x).le) hL
  let hf' : ∀ x, 0 < f x := fun x => lt_of_lt_of_le zero_lt_one (hf x)
  let C' := scaledKernel C f hf'
  let d : ℝ := 1 - ‖f‖⁻¹
  obtain ⟨hd,hd1,hrow⟩ := scaled_row_bound ν C f hf heq
  have hp' (z x : X) : 0 ≤ C' (z,x) := (scaledKernel_pos C hC f hf' z x).le
  have hn : ‖kernelOp ν C'‖ < 1 :=
    (kernelOp_norm_le ν C' hp' hd hrow).trans_lt hd1
  have hkernel (x y : X) : rescaledKernel C f hf' (kernelOp ν C') x y =
      l2ResolvedKernel ν C x y := rescaledKernel_eq_l2ResolvedKernel ν C f hf' hL hn x y
  have hp (x y : X) : 0 < l2ResolvedKernel ν C x y :=
    (hC y x).trans_le (l2ResolvedKernel_ge ν C (fun z x => (hC z x).le) hL x y)
  refine ⟨fun i j => hp _ _, ?_⟩
  have hev := sampleOp_eventually_norm_le ν C' hp' hd
    (show d < (1+d)/2 by dsimp [d]; linarith) hrow
  have hr : ∀ᶠ n in atTop, ∀ x, sampleOp ν (quantize n) C' 1 x ≤ (1+d)/2 := by
    filter_upwards [hev] with n hnn x
    calc
      sampleOp ν (quantize n) C' 1 x ≤ ‖sampleOp ν (quantize n) C' 1 x‖ := le_abs_self _
      _ ≤ ‖sampleOp ν (quantize n) C' 1‖ := ContinuousMap.norm_coe_le_norm _ _
      _ ≤ ‖sampleOp ν (quantize n) C'‖ * ‖(1 : C(X, ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (1+d)/2 := by simpa using hnn
  obtain ⟨N,hN⟩ := eventually_atTop.mp hr
  apply onePositiveSquare_of_entrywise_tendsto
    (A := fun n => Matrix.of fun i j =>
      (rescaledKernel C f hf' (sampleOp ν (quantize (n+N)) C') (s i) (s j))⁻¹)
  · intro n
    exact (sampled_rescaled_reciprocal ν (quantize (n+N)) C hC hsym hP f hf'
      (show 0 ≤ (1+d)/2 by dsimp [d]; linarith)
      (show (1+d)/2 < 1 by dsimp [d]; linarith)
      (hN _ (Nat.le_add_left _ _)) s).2
  · intro i j
    have ht := rescaledKernel_tendsto ν C (fun z x => (hC z x).le) f hf' hd hd1 hrow (s i) (s j)
    rw [hkernel] at ht
    exact (ht.inv₀ (hp _ _).ne').comp (tendsto_add_atTop_nat N)

lemma l2ResolvedKernel_eq_inner (C : C(X × X, ℝ))
    (hsym : ∀ x y, C (x,y) = C (y,x)) (x y : X) :
    l2ResolvedKernel ν C x y = C (x,y) +
      inner ℝ (ContinuousMap.toLp 2 ν ℝ (C.curry x))
        (resolvent (l2Op ν C) (ContinuousMap.toLp 2 ν ℝ (C.curry y))) := by
  unfold l2ResolvedKernel
  rw [hsym y x, l2SectionOp_apply, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (C.curry x)] with z hz
  rw [hz]
  change C (z,x) * _ = _ * C (x,z)
  rw [hsym z x, mul_comm]

end StrictHotSpots.CompactKernel




open MeasureTheory Filter
open scoped Topology ENNReal
namespace StrictHotSpots.L2Limits
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma norm_sq_eq_integral_sq (f : Lp ℝ 2 ν) :
    ‖f‖ ^ 2 = ∫ x, (f x)^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  change (∫ x, f x * f x ∂ν) = _
  simp only [pow_two]

lemma norm_toLp_sub_sq {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x)^2 ∂ν := by
  rw [norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hx hfx hgx
  simp only [hx, hfx, hgx, Pi.sub_apply]

lemma tendsto_toLp_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → X → ℝ} {g b : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 ν) (hg : MemLp g 2 ν) (hb : MemLp b 2 ν)
    (hdom : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 (hg.toLp g)) := by
  have ht : Tendsto (fun n => ∫ x, (f n x - g x)^2 ∂ν) l (𝓝 0) := by
    have hm : ∀ᶠ n in l, AEStronglyMeasurable (fun x => (f n x-g x)^2) ν :=
      Eventually.of_forall fun n => ((hf n).sub hg).aestronglyMeasurable.pow 2
    have hd : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖(f n x-g x)^2‖ ≤ (b x+‖g x‖)^2 := by
      filter_upwards [hdom] with n hn
      filter_upwards [hn] with x hx
      have h1 : ‖f n x-g x‖ ≤ b x+‖g x‖ :=
        by linarith [norm_sub_le (f n x) (g x)]
      rw [Real.norm_eq_abs, abs_pow, ← Real.norm_eq_abs]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hl : ∀ᵐ x ∂ν, Tendsto (fun n => (f n x-g x)^2) l (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with x hx
      simpa using (hx.sub_const (g x)).pow 2
    simpa using tendsto_integral_filter_of_dominated_convergence
      (fun x => (b x+‖g x‖)^2) hm hd (hb.add hg.norm).integrable_sq hl
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) l (𝓝 0) := by
    simpa only [norm_toLp_sub_sq] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr

lemma tendsto_L2_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (f : ι → Lp ℝ 2 ν) (g b : Lp ℝ 2 ν)
    (hdom : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto f l (𝓝 g) := by
  have ht := tendsto_toLp_of_dominated (fun n => Lp.memLp (f n)) (Lp.memLp g)
    (Lp.memLp b) hdom hlim
  simpa only [Lp.toLp_coeFn] using ht

end StrictHotSpots.L2Limits

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma l2Op_ae_integral (C : C(X × X, ℝ)) (f : Lp ℝ 2 ν) :
    ∀ᵐ x ∂ν, l2Op ν C f x = ∫ z, C (z,x) * f z ∂ν := by
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (l2SectionOp ν C f)]
    with x hx
  exact hx.trans (l2SectionOp_apply ν C f x)

lemma l2Op_abs_domination (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ x, ∀ᵐ z ∂ν, C (z,x) ≤ G z x)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (f : Lp ℝ 2 ν) : |l2Op ν C f| ≤ T |f| := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [l2Op_ae_integral ν C f, hT |f|, Lp.coeFn_abs (l2Op ν C f)]
    with x hx htx hax
  rw [hax, hx, htx]
  calc
    |∫ z, C (z,x) * f z ∂ν| ≤ ∫ z, ‖C (z,x) * f z‖ ∂ν :=
      by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => C (z,x) * f z)
    _ ≤ ∫ z, G z x * (|f|) z ∂ν := by
      apply integral_mono_ae
      · exact (ContinuousMap.memLp (p := (2 : ℝ≥0∞)) ν ℝ
          (⟨fun z => C (z,x), C.continuous.comp (continuous_id.prodMk continuous_const)⟩ : C(X,ℝ))).integrable_mul (Lp.memLp f) |>.norm
      · exact (hG x).integrable_mul (Lp.memLp |f|)
      · filter_upwards [hdom x, Lp.coeFn_abs f] with z hz hfz
        rw [hfz, norm_mul, Real.norm_eq_abs, abs_of_nonneg (hC z x), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)

lemma norm_l2Op_le_of_domination (C : C(X × X, ℝ)) (hC : ∀ z x, 0 ≤ C (z,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ x, ∀ᵐ z ∂ν, C (z,x) ≤ G z x)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν) :
    ‖l2Op ν C‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
  intro f
  calc
    ‖l2Op ν C f‖ ≤ ‖T |f|‖ :=
      norm_le_norm_of_abs_le_abs ((l2Op_abs_domination ν C hC G hG hdom T hT f).trans
        (le_abs_self _))
    _ ≤ ‖T‖ * ‖f‖ := by simpa only [norm_abs_eq_norm] using T.le_opNorm |f|

lemma l2Op_strong_tendsto_of_dominated
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (f : Lp ℝ 2 ν) :
    Tendsto (fun n => l2Op ν (C n) f) atTop (𝓝 (T f)) := by
  apply L2Limits.tendsto_L2_of_dominated _ _ (T |f|)
  · apply Eventually.of_forall
    intro n
    have hd := (Lp.coeFn_le _ _).mpr (l2Op_abs_domination ν (C n) (hC n) G hG
      (hdom n) T hT f)
    filter_upwards [hd, Lp.coeFn_abs (l2Op ν (C n) f)] with x hx hax
    simpa only [hax, Real.norm_eq_abs] using hx
  · have he : ∀ᵐ x ∂ν, ∀ n, l2Op ν (C n) f x = ∫ z, C n (z,x) * f z ∂ν :=
      ae_all_iff.mpr fun n => l2Op_ae_integral ν (C n) f
    filter_upwards [he, hT f] with x hx htx
    simp only [hx, htx]
    apply tendsto_integral_of_dominated_convergence (fun z => G z x * ‖f z‖)
    · intro n
      exact ((C n).continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f)
    · exact (hG x).integrable_mul (Lp.memLp f).norm
    · intro n
      filter_upwards [hdom n x] with z hz
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hC n z x)]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    · filter_upwards [hlim x] with z hz
      exact hz.mul_const (f z)

end StrictHotSpots.CompactKernel

namespace StrictHotSpots.BanachResolvent
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_strong_tendsto_moving (A : E →L[ℝ] E) (Q : ℕ → E →L[ℝ] E)
    {d : ℝ} (hd : d < 1) (hA : ‖A‖ < 1)
    (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v)))
    {v : ℕ → E} {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => resolvent (Q n) (v n)) atTop (𝓝 (resolvent A w)) := by
  have hz : Tendsto (fun n => resolvent (Q n) (v n-w)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => (1-d)⁻¹ * ‖v n-w‖) atTop (𝓝 0) := by
      simpa using (hv.sub_const w).norm.const_mul (1-d)⁻¹
    apply squeeze_zero_norm' _ hb
    filter_upwards [hQ] with n hn
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (resolvent_norm_le (Q n) hn hd) (norm_nonneg _))
  have ht := hz.add (resolvent_strong_tendsto A Q hd hA hQ hs w)
  simpa only [map_sub, sub_add_cancel, zero_add] using ht

end StrictHotSpots.BanachResolvent

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma l2Sections_tendsto_of_dominated
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (x : X) :
    Tendsto (fun n => ContinuousMap.toLp 2 ν ℝ ((C n).curry x)) atTop
      (𝓝 ((hG x).toLp (fun z => G z x))) := by
  apply L2Limits.tendsto_L2_of_dominated _ _ ((hG x).toLp (fun z => G z x))
  · apply Eventually.of_forall
    intro n
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν ((C n).curry x),
      (hG x).coeFn_toLp, hdom n x] with z hz hgz hdz
    rw [hz, hgz]
    change ‖C n (x,z)‖ ≤ G z x
    rw [hsym n x z, Real.norm_eq_abs, abs_of_nonneg (hC n z x)]
    exact hdz
  · have he : ∀ᵐ z ∂ν, ∀ n,
        ContinuousMap.toLp 2 ν ℝ ((C n).curry x) z = C n (x,z) :=
      ae_all_iff.mpr fun n => ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν ((C n).curry x)
    filter_upwards [he, (hG x).coeFn_toLp, hlim x] with z hz hgz hlz
    simpa only [hz, hgz, hsym] using hlz



def singularResolvedKernel (G : X → X → ℝ)
    (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (x y : X) : ℝ :=
  G x y + inner ℝ ((hG x).toLp (fun z => G z x))
    (resolvent T ((hG y).toLp (fun z => G z y)))

lemma l2ResolvedKernel_tendsto_of_dominated
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (hsub : ‖T‖ < 1) (x y : X)
    (hxy : Tendsto (fun n => C n (x,y)) atTop (𝓝 (G x y))) :
    Tendsto (fun n => l2ResolvedKernel ν (C n) x y) atTop
      (𝓝 (singularResolvedKernel ν G hG T x y)) := by
  have hs := l2Sections_tendsto_of_dominated ν C hC hsym G hG hdom hlim
  have hop := l2Op_strong_tendsto_of_dominated ν C hC G hG hdom hlim T hT
  have hb : ∀ᶠ n in atTop, ‖l2Op ν (C n)‖ ≤ ‖T‖ :=
    Eventually.of_forall fun n => norm_l2Op_le_of_domination ν (C n) (hC n) G hG
      (hdom n) T hT
  have hr := resolvent_strong_tendsto_moving T (fun n => l2Op ν (C n))
    hsub hsub hb hop (hs y)
  have ht := hxy.add ((hs x).inner hr)
  simpa only [singularResolvedKernel, l2ResolvedKernel_eq_inner ν _ (hsym _)] using ht

lemma singularResolvedKernel_ge
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 ≤ C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (hsub : ‖T‖ < 1) (x y : X)
    (hxy : Tendsto (fun n => C n (x,y)) atTop (𝓝 (G x y))) :
    G x y ≤ singularResolvedKernel ν G hG T x y := by
  apply le_of_tendsto_of_tendsto hxy
    (l2ResolvedKernel_tendsto_of_dominated ν C hC hsym G hG hdom hlim T hT hsub x y hxy)
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [hsym n x y]
    exact l2ResolvedKernel_ge ν (C n) (hC n)
      ((norm_l2Op_le_of_domination ν (C n) (hC n) G hG (hdom n) T hT).trans_lt hsub) x y





theorem singular_reciprocal_of_regularization [Nonempty X] [DecidableEq X]
    (C : ℕ → C(X × X, ℝ)) (hC : ∀ n z x, 0 < C n (z,x))
    (hsym : ∀ n x y, C n (x,y) = C n (y,x))
    (hP : ∀ n (ι : Type) [Fintype ι] (s : ι → X),
      OnePositiveSquare (Matrix.of fun i j => (C n (s i,s j))⁻¹))
    (G : X → X → ℝ) (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (hpos : ∀ x y, x ≠ y → 0 < G x y)
    (hdom : ∀ n x, ∀ᵐ z ∂ν, C n (z,x) ≤ G z x)
    (hlim : ∀ x, ∀ᵐ z ∂ν, Tendsto (fun n => C n (z,x)) atTop (𝓝 (G z x)))
    (hoff : ∀ x y, x ≠ y → Tendsto (fun n => C n (x,y)) atTop (𝓝 (G x y)))
    (hdiag : ∀ x, Tendsto (fun n => C n (x,x)) atTop atTop)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hT : ∀ f : Lp ℝ 2 ν, ∀ᵐ x ∂ν, T f x = ∫ z, G z x * f z ∂ν)
    (hsub : ‖T‖ < 1) {ι : Type} [Fintype ι] (s : ι → X) :
    OnePositiveSquare (Matrix.of fun i j =>
      if s i = s j then 0 else (singularResolvedKernel ν G hG T (s i) (s j))⁻¹) := by
  classical
  have hCn : ∀ n z x, 0 ≤ C n (z,x) := fun n z x => (hC n z x).le
  have hb (n : ℕ) : ‖l2Op ν (C n)‖ < 1 :=
    (norm_l2Op_le_of_domination ν (C n) (hCn n) G hG (hdom n) T hT).trans_lt hsub
  apply onePositiveSquare_of_entrywise_tendsto
    (A := fun n => Matrix.of fun i j => (l2ResolvedKernel ν (C n) (s i) (s j))⁻¹)
  · intro n
    exact (compact_reciprocal_of_l2_norm_lt_one ν (C n) (hC n) (hsym n) (hP n) (hb n) s).2
  · intro i j
    dsimp only [Matrix.of_apply]
    split_ifs with hij
    · have ht : Tendsto (fun n => l2ResolvedKernel ν (C n) (s i) (s j)) atTop atTop := by
        apply tendsto_atTop_mono _ (hdiag (s i))

        intro n
        simpa only [← hij] using l2ResolvedKernel_ge ν (C n) (hCn n) (hb n) (s i) (s i)
      exact tendsto_inv_atTop_zero.comp ht
    · have hp := (hpos (s i) (s j) hij).trans_le
        (singularResolvedKernel_ge ν C hCn hsym G hG hdom hlim T hT hsub
          (s i) (s j) (hoff (s i) (s j) hij))
      exact (l2ResolvedKernel_tendsto_of_dominated ν C hCn hsym G hG hdom hlim T hT hsub
        (s i) (s j) (hoff (s i) (s j) hij)).inv₀ hp.ne'

end StrictHotSpots.CompactKernel

end SingularLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section SquaredDistanceKernelLayer
noncomputable section
open Set Filter Topology
open scoped BigOperators InnerProductSpace
open scoped NNReal
namespace SquaredDistanceKernel

universe u
variable {X : Type u}


def ConditionallyNegative (D : Matrix X X ℝ) : Prop :=
  D.IsHermitian ∧ (∀ x, D x x = 0) ∧
    ∀ c : X →₀ ℝ, c.sum (fun _ a => a) = 0 →
      c.sum (fun x a => c.sum (fun y b => a * D x y * b)) ≤ 0

def anchored (D : Matrix X X ℝ) (o : X) : Matrix X X ℝ :=
  Matrix.of fun x y => (D x o + D y o - D x y) / 2

lemma anchor_sum_identity (D : X → X → ℝ) (o : X) (c : X →₀ ℝ) : (c.sum (fun x a => c.sum (fun y b => a * ((D x o + D y o - D x y) / 2) * b))) =
    ((c.sum (fun x a => a * D x o * (c.sum fun _ b => b))) +
     (c.sum (fun y b => (c.sum fun _ a => a) * D y o * b)) -
     (c.sum (fun x a => c.sum (fun y b => a * D x y * b)))) / 2 := by
  calc
    _ = c.sum (fun x a => c.sum (fun y b =>
        (a * D x o * b + a * D y o * b - a * D x y * b) / 2)) := by
      apply Finsupp.sum_congr
      intro x hx
      apply Finsupp.sum_congr
      intro y hy
      ring
    _ = _ := by
      simp only [Finsupp.sum]
      simp only [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      congr 2
      congr 1
      · simp only [← Finset.mul_sum]
      · rw [Finset.sum_comm]
        simp only [← Finset.sum_mul]

lemma anchored_posSemidef {D : Matrix X X ℝ} (hD : ConditionallyNegative D) (o : X) :
    (anchored D o).PosSemidef := by
  classical
  have hs (x y : X) : D x y = D y x := by
    simpa using (hD.1.apply x y).symm
  refine ⟨?_, ?_⟩
  · ext x y
    simp [Matrix.conjTranspose_apply, anchored, hs y x, add_comm]
  · intro c
    change 0 ≤ c.sum (fun x a => c.sum (fun y b => a * ((D x o + D y o - D x y) / 2) * b))
    let m := c.sum (fun _ a => a)
    have hm : (c - Finsupp.single o m).sum (fun _ a => a) = 0 := by
      simp [Finsupp.sum_sub_index, m]
    have hh := hD.2.2 (c - Finsupp.single o m) hm
    simp [Finsupp.sum_sub_index, sub_mul, mul_sub, Finsupp.sum_sub,
      zero_mul, mul_zero, Finsupp.sum_single_index,
      hD.2.1, hs o, sub_zero] at hh
    dsimp [m] at hh
    rw [anchor_sum_identity (fun x y => D x y) o c]
    linarith

def lifted (G : Matrix X X ℝ) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => G x y • ContinuousLinearMap.id ℝ ℝ

lemma lifted_posSemidef {G : Matrix X X ℝ} (hG : G.PosSemidef) :
    (lifted G).PosSemidef := by
  have hs (x y : X) : G y x = G x y := by simpa using hG.1.apply x y
  apply (RKHS.posSemidef_tfae.out 1 3).mpr
  refine ⟨?_, ?_⟩
  · ext x y
    simp [Matrix.conjTranspose_apply, lifted, star_smul,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id, hs]
  · intro c
    simpa [lifted, RCLike.inner_apply, hs, mul_comm, mul_left_comm, mul_assoc] using hG.2 c

lemma positive_kernel_realization {G : Matrix X X ℝ} (hG : G.PosSemidef) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (b : X → H), ∀ x y, inner ℝ (b x) (b y) = G x y := by
  let K := lifted G
  let : Fact K.PosSemidef := ⟨lifted_posSemidef hG⟩
  let H := RKHS.OfKernel K
  refine ⟨H, inferInstance, inferInstance, inferInstance, fun x => RKHS.kerFun H x 1, ?_⟩
  intro x y
  rw [← RKHS.kernel_inner]
  change inner ℝ (RKHS.kernel (RKHS.OfKernel K) y x 1) 1 = G x y
  rw [RKHS.OfKernel.kernel_ofKernel (K := K)]
  simp [K, lifted, RCLike.inner_apply,
    show G y x = G x y by simpa using hG.1.apply x y]
lemma squared_distance_realization {D : Matrix X X ℝ}
    (hD : ConditionallyNegative D) (o : X) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (b : X → H), ∀ x y, ‖b x - b y‖ ^ 2 = D x y := by
  obtain ⟨H, hn, hi, hc, b, hb⟩ := positive_kernel_realization (anchored_posSemidef hD o)
  let := hn
  let := hi
  let := hc
  refine ⟨H, hn, hi, hc, b, ?_⟩
  intro x y
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    hb, hb, hb]
  simp only [anchored, Matrix.of_apply, hD.2.1]
  ring

lemma injective_of_distance_positive {H : Type*} [NormedAddCommGroup H]
    {D : Matrix X X ℝ} {b : X → H} (hb : ∀ x y, ‖b x - b y‖ ^ 2 = D x y)
    (hpos : ∀ x y, x ≠ y → 0 < D x y) : Function.Injective b := by
  intro x y heq
  by_contra hne
  have hh := hpos x y hne
  rw [← hb x y, heq, sub_self, norm_zero, zero_pow (by decide)] at hh
  exact lt_irrefl _ hh

lemma lipschitz_of_distance_bound [PseudoMetricSpace X] {H : Type*}
    [NormedAddCommGroup H] {D : Matrix X X ℝ} {b : X → H} {C : ℝ≥0}
    (hb : ∀ x y, ‖b x - b y‖ ^ 2 = D x y)
    (hbound : ∀ x y, D x y ≤ C ^ 2 * dist x y ^ 2) : LipschitzWith C b := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg C.coe_nonneg dist_nonneg)).mp
  rw [mul_pow, hb]
  exact hbound x y




lemma separable_lipschitz_embedding [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] {D : Matrix X X ℝ}
    (hD : ConditionallyNegative D) (o : X) {C : ℝ≥0}
    (hpos : ∀ x y, x ≠ y → 0 < D x y)
    (hbound : ∀ x y, D x y ≤ (C : ℝ) ^ 2 * dist x y ^ 2) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H) (b : X → H),
      Function.Injective b ∧ LipschitzWith C b ∧ ∀ x y, ‖b x - b y‖ ^ 2 = D x y := by
  obtain ⟨H, hn, hi, hc, b, hb⟩ := squared_distance_realization hD o
  let := hn
  let := hi
  let := hc
  have hl := lipschitz_of_distance_bound hb hbound
  let S := (Submodule.span ℝ (Set.range b)).topologicalClosure
  have hsep : TopologicalSpace.IsSeparable (S : Set H) := by
    rw [Submodule.topologicalClosure_coe]
    exact ((TopologicalSpace.isSeparable_range hl.continuous).span (R := ℝ)).closure
  let := hsep.separableSpace
  let b' : X → S := fun x => ⟨b x,
    (Submodule.span ℝ (Set.range b)).le_topologicalClosure (Submodule.subset_span ⟨x, rfl⟩)⟩
  have hb' (x y : X) : ‖b' x - b' y‖ ^ 2 = D x y := hb x y
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, b',
    injective_of_distance_positive hb' hpos, lipschitz_of_distance_bound hb' hbound, hb'⟩

end SquaredDistanceKernel
end
end SquaredDistanceKernelLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
