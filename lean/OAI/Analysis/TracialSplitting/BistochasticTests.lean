import OAI.Analysis.TracialSplitting.NuclearFamilies

namespace OAI


section

noncomputable section

open Pureness

open scoped ComplexOrder

namespace CurrentMain

structure BistochasticTest (A : Type) [CStarAlgebra A] where
  size : ℕ
  coeff : Fin size → A
  col : ∑ i, star (coeff i)*coeff i = 1
  row : ∑ i, coeff i*star (coeff i) = 1

namespace BistochasticTest

variable {A D : Type} [CStarAlgebra A] [CStarAlgebra D]

def map (V : BistochasticTest A) (ι : A →⋆ₐ[ℂ] D) : BistochasticTest D where
  size := V.size
  coeff := fun i => ι (V.coeff i)
  col := by simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι V.col
  row := by simpa only [map_sum,map_mul,map_star,map_one] using congrArg ι V.row

def single (u : unitary A) : BistochasticTest A where
  size := 1
  coeff := fun _ => (u : A)
  col := by simp only [Fin.sum_univ_one]; exact Unitary.coe_star_mul_self u
  row := by simp only [Fin.sum_univ_one]; exact Unitary.coe_mul_star_self u

variable [PartialOrder D] [StarOrderedRing D]

def energy (V : BistochasticTest D) (τ : TracialState D) (p : D) : ℝ :=
  ∑ i, traceTwoNorm τ (V.coeff i*p-p*V.coeff i)^2

omit [StarOrderedRing D] in
lemma energy_nonneg (V : BistochasticTest D) (τ : TracialState D) (p : D) :
    0 ≤ V.energy τ p := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sum_mul_energy (V : BistochasticTest D) (τ : TracialState D) (d : D) :
    (∑ i, traceTwoNorm τ (V.coeff i*d)^2) = traceTwoNorm τ d^2 := by
  simp only [traceTwoNorm_sq,star_mul,mul_assoc,← Complex.re_sum,← map_sum]
  congr 2
  simp only [← mul_assoc (star (V.coeff _)) _ _,← Finset.sum_mul,← Finset.mul_sum,V.col,one_mul]

lemma sum_energy_mul (V : BistochasticTest D) (τ : TracialState D) (d : D) :
    (∑ i, traceTwoNorm τ (d*V.coeff i)^2) = traceTwoNorm τ d^2 := by
  simp only [traceTwoNorm_sq,star_mul]
  have he (i : Fin V.size) :
      τ.functional (star (V.coeff i)*star d*(d*V.coeff i)) =
        τ.functional (star d*d*(V.coeff i*star (V.coeff i))) := by
    rw [mul_assoc,τ.tracial (star (V.coeff i))]
    congr 1
    noncomm_ring
  simp_rw [he]
  rw [← Complex.re_sum,← map_sum,← Finset.mul_sum,V.row,mul_one]

lemma square_add_le (τ : TracialState D) (a b : D) :
    traceTwoNorm τ (a+b)^2 ≤ 2*traceTwoNorm τ a^2+2*traceTwoNorm τ b^2 := by
  have h := traceTwoNorm_add_le τ a b
  have h0 := traceTwoNorm_nonneg τ (a+b)
  have h1 := traceTwoNorm_nonneg τ a
  have h2 := traceTwoNorm_nonneg τ b
  nlinarith [sq_nonneg (traceTwoNorm τ a-traceTwoNorm τ b)]

lemma energy_le (V : BistochasticTest D) (τ : TracialState D) (d : D) :
    V.energy τ d ≤ 4*traceTwoNorm τ d^2 := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    square_add_le τ (V.coeff i*d) (-(d*V.coeff i))
  simp only [← sub_eq_add_neg,traceTwoNorm_neg,Finset.sum_add_distrib,← Finset.mul_sum,
    V.sum_mul_energy τ d,V.sum_energy_mul τ d] at h
  dsimp [energy]
  linarith

lemma energy_perturb (V : BistochasticTest D) (τ : TracialState D) (t y : D) :
    V.energy τ t ≤ 2*V.energy τ y+8*traceTwoNorm τ (t-y)^2 := by
  have he (i : Fin V.size) : V.coeff i*t-t*V.coeff i =
      (V.coeff i*y-y*V.coeff i)+(V.coeff i*(t-y)-(t-y)*V.coeff i) := by noncomm_ring
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    square_add_le τ (V.coeff i*y-y*V.coeff i) (V.coeff i*(t-y)-(t-y)*V.coeff i)
  simp only [← he,Finset.sum_add_distrib,← Finset.mul_sum] at h
  change V.energy τ t ≤ 2*V.energy τ y+2*V.energy τ (t-y) at h
  linarith [V.energy_le τ (t-y)]

lemma overlap_le (V : BistochasticTest D) (τ : TracialState D) {z : D}
    (hz : IsStarProjection z) :
    (τ.functional (z*weightedAverage (fun _ : Fin V.size => (1 : ℝ)) V.coeff (1-z))).re ≤
      V.energy τ z := by
  rw [weightedAverage_overlap τ _ _ hz hz.one_sub]
  simp only [one_mul]
  apply Finset.sum_le_sum
  intro i _
  have he : z*V.coeff i*(1-z) = (z*V.coeff i-V.coeff i*z)*(1-z) := by
    noncomm_ring [hz.isIdempotentElem.eq]
  have hn : traceTwoNorm τ (z*V.coeff i*(1-z)) ≤
      traceTwoNorm τ (V.coeff i*z-z*V.coeff i) := by
    rw [he]
    apply (traceTwoNorm_mul_right τ _ _).trans
    rw [traceTwoNorm_sub_swap]
    exact (mul_le_mul_of_nonneg_right hz.one_sub.norm_le (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _)
  exact (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _)).mpr hn

lemma unitary_tests (V : BistochasticTest D) :
    ∃ L : Finset (unitary D), ∀ (J : Type) [Fintype J] (y : J → D)
      (τ : TracialState D) (B : ℝ), 0 ≤ B →
      (∀ u ∈ L, ∑ j, traceTwoNorm τ ((u : D)*y j-y j*(u : D))^2 ≤ B) →
      ∑ j, V.energy τ (y j) ≤ (4*V.size)*B := by
  classical
  choose u c he hc using fun i => CStarAlgebra.exists_sum_four_unitary (V.coeff i)
  let L := Finset.univ.biUnion fun i : Fin V.size => Finset.univ.image (u i)
  refine ⟨L,?_⟩
  intro J _ y τ B _ hB
  have hb (i : Fin V.size) (j : J) :
      traceTwoNorm τ (V.coeff i*y j-y j*V.coeff i)^2 ≤
        ∑ k : Fin 4, traceTwoNorm τ ((u i k : D)*y j-y j*(u i k : D))^2 := by
    have hd : V.coeff i*y j-y j*V.coeff i =
        ∑ k : Fin 4, c i k • ((u i k : D)*y j-y j*(u i k : D)) := by
      rw [he i,Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
      simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
    have hnorm : traceTwoNorm τ (V.coeff i*y j-y j*V.coeff i) ≤
        (1/2 : ℝ)*(∑ k : Fin 4, traceTwoNorm τ ((u i k : D)*y j-y j*(u i k : D))) := by
      rw [hd]
      apply (traceTwoNorm_sum_le _ τ _).trans
      simp only [traceTwoNorm_smul,Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
        ((hc i k).trans (by linarith [kraus_coefficient_norm V.coeff V.col i])) (traceTwoNorm_nonneg τ _)
    have hs := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun k : Fin 4 => traceTwoNorm τ ((u i k : D)*y j-y j*(u i k : D)))
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hs
    have hn := traceTwoNorm_nonneg τ (V.coeff i*y j-y j*V.coeff i)
    have hsum : 0 ≤ ∑ k : Fin 4, traceTwoNorm τ ((u i k : D)*y j-y j*(u i k : D)) :=
      Finset.sum_nonneg fun _ _ => traceTwoNorm_nonneg τ _
    nlinarith
  calc
    _ ≤ ∑ j, ∑ i, ∑ k : Fin 4, traceTwoNorm τ ((u i k : D)*y j-y j*(u i k : D))^2 :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hb i j
    _ = ∑ i, ∑ k : Fin 4, ∑ j, traceTwoNorm τ ((u i k : D)*y j-y j*(u i k : D))^2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ i : Fin V.size, ∑ k : Fin 4, B := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun k _ => hB _ (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    _ = _ := by simp; ring

lemma relative_unitary_tests [PartialOrder A] [StarOrderedRing A]
    (V : BistochasticTest A) (ι : A →⋆ₐ[ℂ] D) :
    ∃ L : Finset (unitary A), ∀ (J : Type) [Fintype J] (y : J → D)
      (τ : TracialState D) (B : ℝ), 0 ≤ B →
      (∀ u ∈ L, ∑ j, traceTwoNorm τ (ι (u : A)*y j-y j*ι (u : A))^2 ≤ B) →
      ∑ j, (V.map ι).energy τ (y j) ≤ (4*V.size)*B := by
  classical
  choose u c he hc using fun i => CStarAlgebra.exists_sum_four_unitary (V.coeff i)
  let L := Finset.univ.biUnion fun i : Fin V.size => Finset.univ.image (u i)
  refine ⟨L,?_⟩
  intro J _ y τ B _ hB
  have hb (i : Fin V.size) (j : J) :
      traceTwoNorm τ (ι (V.coeff i)*y j-y j*ι (V.coeff i))^2 ≤
        ∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))^2 := by
    have hd : ι (V.coeff i)*y j-y j*ι (V.coeff i) =
        ∑ k : Fin 4, c i k • (ι (u i k : A)*y j-y j*ι (u i k : A)) := by
      rw [he i,map_sum]
      simp only [map_smul]
      rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_sub_distrib]
      simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
    have hnorm : traceTwoNorm τ (ι (V.coeff i)*y j-y j*ι (V.coeff i)) ≤
        (1/2 : ℝ)*(∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))) := by
      rw [hd]
      apply (traceTwoNorm_sum_le _ τ _).trans
      simp only [traceTwoNorm_smul,Finset.mul_sum]
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right
        ((hc i k).trans (by linarith [kraus_coefficient_norm V.coeff V.col i])) (traceTwoNorm_nonneg τ _)
    have hs := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun k : Fin 4 => traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A)))
    simp only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] at hs
    have hn := traceTwoNorm_nonneg τ (ι (V.coeff i)*y j-y j*ι (V.coeff i))
    have hsum : 0 ≤ ∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A)) :=
      Finset.sum_nonneg fun _ _ => traceTwoNorm_nonneg τ _
    nlinarith
  calc
    _ ≤ ∑ j, ∑ i, ∑ k : Fin 4, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))^2 :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ => hb i j
    _ = ∑ i, ∑ k : Fin 4, ∑ j, traceTwoNorm τ (ι (u i k : A)*y j-y j*ι (u i k : A))^2 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ ≤ ∑ i : Fin V.size, ∑ k : Fin 4, B := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun k _ => hB _ (Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩)
    _ = _ := by simp; ring

end BistochasticTest

end CurrentMain

end

end

end OAI
