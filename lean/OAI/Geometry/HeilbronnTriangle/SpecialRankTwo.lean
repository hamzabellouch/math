import OAI.Geometry.HeilbronnTriangle.LatticePacking
import OAI.Geometry.HeilbronnTriangle.SpecialNormals

namespace OAI


namespace Problem355.SpecialRankTwo

open scoped BigOperators

theorem sum_weights_le {α : Type*} (A : Finset α) (W : α → ℝ)
    (M C : ℝ) (hM : 0 ≤ M) (hW : ∀ a ∈ A, W a ≤ M)
    (hc : (A.card : ℝ) ≤ C) : ∑ a ∈ A, W a ≤ M * C := by
  calc
    ∑ a ∈ A, W a ≤ ∑ _a ∈ A, M := Finset.sum_le_sum hW
    _ = M * (A.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_comm _ _
    _ ≤ M * C := mul_le_mul_of_nonneg_left hc hM

theorem weighted_bound_of_covol_cube {T N R I h M J : ℝ}
    (_hN : 0 ≤ N) (hR : 0 < R) (hI : 0 < I) (hM : 0 ≤ M)
    (hJ : 0 < J) (hcov : I ^ 2 * R ^ 3 ≤ h ^ 2 * J ^ 3)
    (hcount : T ≤ M * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3) :
    T ≤ (144 * Real.pi) ^ 3 * M * N ^ 6 * h ^ 2 / (I ^ 2 * R ^ 3) := by
  have hden : 0 < I ^ 2 * R ^ 3 := by positivity
  have hinv : 1 / J ^ 3 ≤ h ^ 2 / (I ^ 2 * R ^ 3) := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    simpa using hcov
  calc
    T ≤ M * (9 * Real.pi * (4 * N) ^ 2 / J) ^ 3 := hcount
    _ = ((144 * Real.pi) ^ 3 * M * N ^ 6) * (1 / J ^ 3) := by ring
    _ ≤ ((144 * Real.pi) ^ 3 * M * N ^ 6) *
        (h ^ 2 / (I ^ 2 * R ^ 3)) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = _ := by ring

section OnePlane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weighted_spanning_triples_le
    (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Finset (Fin 3 → L)) (W : (Fin 3 → L) → ℝ)
    (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ R)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)])
    (hW : ∀ a ∈ A, W a ≤ M) :
    ∑ a ∈ A, W a ≤ M * (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 := by
  have hc : (A.card : ℝ) ≤ (9 * Real.pi * R ^ 2 / ZLattice.covolume L) ^ 3 :=
    LatticePacking.plane_spanning_triples_card_le (E := E) hdim L A R hR hA hpair
  exact sum_weights_le A W M _ hM hW hc

theorem weighted_spanning_triples_le_shell
    (hdim : Module.finrank ℝ E = 2)
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (A : Finset (Fin 3 → L)) (W : (Fin 3 → L) → ℝ)
    (N R I h M : ℝ) (hN : 0 ≤ N) (hR : 0 < R) (hI : 0 < I)
    (hM : 0 ≤ M)
    (hA : ∀ a ∈ A, ∀ i, ‖(a i : E)‖ ≤ 4 * N)
    (hpair : ∀ a ∈ A, ∃ i j : Fin 3,
      LinearIndependent ℝ ![(a i : E), (a j : E)])
    (hW : ∀ a ∈ A, W a ≤ M)
    (hcov : I ^ 2 * R ^ 3 ≤ h ^ 2 * ZLattice.covolume L ^ 3) :
    ∑ a ∈ A, W a ≤ (144 * Real.pi) ^ 3 * M * N ^ 6 * h ^ 2 /
      (I ^ 2 * R ^ 3) := by
  exact weighted_bound_of_covol_cube hN hR hI hM
    (ZLattice.covolume_pos L MeasureTheory.volume) hcov
    (weighted_spanning_triples_le hdim L A W (4 * N) M
      (by positivity) hM hA hpair hW)

end OnePlane

theorem covolume_cube_lower {I R r g h J : ℝ}
    (hI : 0 < I) (hR : 0 ≤ R) (hr : R ≤ r) (hg : 0 < g)
    (hJ : J = I * r / g) (hg3 : g ^ 3 ≤ I * h ^ 2) :
    I ^ 2 * R ^ 3 ≤ h ^ 2 * J ^ 3 := by
  have hr0 : 0 ≤ r := hR.trans hr
  have hpow : R ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hR hr 3
  have hmul : I ^ 2 * R ^ 3 * g ^ 3 ≤ I ^ 3 * r ^ 3 * h ^ 2 := by
    calc
      I ^ 2 * R ^ 3 * g ^ 3 ≤ I ^ 2 * r ^ 3 * g ^ 3 := by gcongr
      _ ≤ I ^ 2 * r ^ 3 * (I * h ^ 2) :=
        mul_le_mul_of_nonneg_left hg3 (by positivity)
      _ = _ := by ring
  rw [hJ, div_pow, ← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < g ^ 3)).mpr
  nlinarith only [hmul]

theorem special_rank_two_shell
    (E : (Fin 3 → ℤ) → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
    [∀ x, FiniteDimensional ℝ (E x)]
    [∀ x, MeasurableSpace (E x)] [∀ x, BorelSpace (E x)]
    (L : ∀ x, Submodule ℤ (E x))
    [∀ x, DiscreteTopology (L x)] [∀ x, IsZLattice ℝ (L x)]
    (S : Finset (Fin 3 → ℤ))
    (A : ∀ x, Finset (Fin 3 → L x))
    (W : ∀ x, (Fin 3 → L x) → ℝ)
    (R q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t,
      -((2 * R : ℕ) : ℤ) ≤ x t ∧ x t ≤ ((2 * R : ℕ) : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (N I h Cw : ℝ) (hN : 0 ≤ N) (hI : 0 < I) (hCw : 0 ≤ Cw)
    (hparam : h ^ 14 ≤ (q : ℝ))
    (hdim : ∀ x ∈ S, Module.finrank ℝ (E x) = 2)
    (hA : ∀ x ∈ S, ∀ a ∈ A x, ∀ t, ‖(a t : E x)‖ ≤ 4 * N)
    (hpair : ∀ x ∈ S, ∀ a ∈ A x, ∃ s t : Fin 3,
      LinearIndependent ℝ ![(a s : E x), (a t : E x)])
    (hW : ∀ x ∈ S, ∀ a ∈ A x, W x a ≤ Cw * (q : ℝ) * h ^ 12)
    (hcov : ∀ x ∈ S,
      I ^ 2 * (R : ℝ) ^ 3 ≤ h ^ 2 * ZLattice.covolume (L x) ^ 3) :
    ∑ x ∈ S, ∑ a ∈ A x, W x a ≤
      512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2 := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  let F : ℝ := (144 * Real.pi) ^ 3 * (Cw * (q : ℝ) * h ^ 12) *
    N ^ 6 * h ^ 2 / (I ^ 2 * (R : ℝ) ^ 3)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfiber : ∀ x ∈ S, ∑ a ∈ A x, W x a ≤ F := by
    intro x hx
    exact weighted_spanning_triples_le_shell (hdim x hx) (L x) (A x) (W x)
      N R I h (Cw * (q : ℝ) * h ^ 12) hN hRreal hI (by positivity)
      (hA x hx) (hpair x hx) (hW x hx) (hcov x hx)
  have hcard : (S.card : ℝ) ≤ 512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) ≤ 64 * ((2 * R : ℕ) : ℝ) ^ 3 / (q : ℝ) ^ 2 :=
        SpecialNormals.card_exceptional_normals_le S (2 * R) q hq
          i j k hki hkj hbox hnonzero hline
      _ = _ := by push_cast; ring
  have hratio : h ^ 14 / (q : ℝ) ≤ 1 :=
    (div_le_one hqreal).mpr hparam
  calc
    ∑ x ∈ S, ∑ a ∈ A x, W x a ≤ ∑ _x ∈ S, F :=
      Finset.sum_le_sum hfiber
    _ = (S.card : ℝ) * F := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2) * F :=
      mul_le_mul_of_nonneg_right hcard hF
    _ = (512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2) *
        (h ^ 14 / (q : ℝ)) := by
      dsimp [F]
      field_simp
    _ ≤ (512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

theorem special_rank_two_shell_subtype
    (S : Finset (Fin 3 → ℤ)) (E : S → Type*)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
    [∀ x, FiniteDimensional ℝ (E x)]
    [∀ x, MeasurableSpace (E x)] [∀ x, BorelSpace (E x)]
    (L : ∀ x, Submodule ℤ (E x))
    [∀ x, DiscreteTopology (L x)] [∀ x, IsZLattice ℝ (L x)]
    (A : ∀ x, Finset (Fin 3 → L x))
    (W : ∀ x, (Fin 3 → L x) → ℝ)
    (R q : ℕ) (hR : 0 < R) (hq : 0 < q)
    (i j k : Fin 3) (hki : k ≠ i) (hkj : k ≠ j)
    (hbox : ∀ x ∈ S, ∀ t,
      -((2 * R : ℕ) : ℤ) ≤ x t ∧ x t ≤ ((2 * R : ℕ) : ℤ))
    (hnonzero : ∀ x ∈ S, x k ≠ 0)
    (hline : ∀ x ∈ S, (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1})
    (N I h Cw : ℝ) (hN : 0 ≤ N) (hI : 0 < I) (hCw : 0 ≤ Cw)
    (hparam : h ^ 14 ≤ (q : ℝ))
    (hdim : ∀ x, Module.finrank ℝ (E x) = 2)
    (hA : ∀ x, ∀ a ∈ A x, ∀ t, ‖(a t : E x)‖ ≤ 4 * N)
    (hpair : ∀ x, ∀ a ∈ A x, ∃ s t : Fin 3,
      LinearIndependent ℝ ![(a s : E x), (a t : E x)])
    (hW : ∀ x, ∀ a ∈ A x, W x a ≤ Cw * (q : ℝ) * h ^ 12)
    (hcov : ∀ x,
      I ^ 2 * (R : ℝ) ^ 3 ≤ h ^ 2 * ZLattice.covolume (L x) ^ 3) :
    ∑ x : S, ∑ a ∈ A x, W x a ≤
      512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2 := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  let F : ℝ := (144 * Real.pi) ^ 3 * (Cw * (q : ℝ) * h ^ 12) *
    N ^ 6 * h ^ 2 / (I ^ 2 * (R : ℝ) ^ 3)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hfiber : ∀ x : S, ∑ a ∈ A x, W x a ≤ F := by
    intro x
    exact weighted_spanning_triples_le_shell (hdim x) (L x) (A x) (W x)
      N R I h (Cw * (q : ℝ) * h ^ 12) hN hRreal hI (by positivity)
      (hA x) (hpair x) (hW x) (hcov x)
  have hcard : (S.card : ℝ) ≤ 512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
    calc
      (S.card : ℝ) ≤ 64 * ((2 * R : ℕ) : ℝ) ^ 3 / (q : ℝ) ^ 2 :=
        SpecialNormals.card_exceptional_normals_le S (2 * R) q hq
          i j k hki hkj hbox hnonzero hline
      _ = _ := by push_cast; ring
  have hratio : h ^ 14 / (q : ℝ) ≤ 1 :=
    (div_le_one hqreal).mpr hparam
  calc
    ∑ x : S, ∑ a ∈ A x, W x a ≤ ∑ _x : S, F :=
      Finset.sum_le_sum (fun x _ => hfiber x)
    _ = (S.card : ℝ) * F := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ ≤ (512 * (R : ℝ) ^ 3 / (q : ℝ) ^ 2) * F :=
      mul_le_mul_of_nonneg_right hcard hF
    _ = (512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2) *
        (h ^ 14 / (q : ℝ)) := by
      dsimp [F]
      field_simp
    _ ≤ (512 * (144 * Real.pi) ^ 3 * Cw * N ^ 6 / I ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := mul_one _

end Problem355.SpecialRankTwo

end OAI
