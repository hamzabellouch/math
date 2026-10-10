import OAI.NumberTheory.CubicMoment.Estimates.PrimaryNormMultiplicity
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticVoronoi
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra

namespace OAI

/-! Energy of the actual cube-completed primal polynomial. Cube-divisor
fibers cost an arbitrary small power; the remaining weighted pair count
is linear in the norm cutoff, because the d-variable has exponent -2. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCubeProduct (du : Eisenstein × Eisenstein) : Eisenstein := du.2*du.1^3

lemma metaplecticCubeProduct_norm (du : Eisenstein × Eisenstein) :
    norm (metaplecticCubeProduct du) = norm du.2*norm du.1^3 := by
  change Complex.normSq ((du.2:ℂ)*(du.1:ℂ)^3) = _
  rw [Complex.normSq_mul,map_pow]
  rfl

def metaplecticCubeCoefficient (S : Finset (Eisenstein × Eisenstein))
    (w : Eisenstein × Eisenstein → ℂ) (b : Eisenstein) : ℂ :=
  ∑ du ∈ S with metaplecticCubeProduct du = b, w du

lemma metaplectic_cube_fiber_card (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) {b : Eisenstein} :
    (S.filter (fun du => metaplecticCubeProduct du = b)).card ≤
      (((S.image Prod.fst).filter (fun d => d ∣ b)).card) := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro du hdu
    obtain ⟨hdu,hb⟩ := Finset.mem_filter.mp hdu
    refine Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hdu,?_⟩
    rw [←hb]
    exact (dvd_pow_self du.1 (by norm_num : (3:ℕ) ≠ 0)).trans
      (dvd_mul_left _ _)
  · intro du hdu ev hev he
    obtain ⟨hdu,hb⟩ := Finset.mem_filter.mp hdu
    obtain ⟨hev,hevb⟩ := Finset.mem_filter.mp hev
    have hd : du.1 ≠ 0 := primary_ne_zero (hS du hdu).1
    apply Prod.ext he
    apply mul_right_cancel₀ (pow_ne_zero 3 hd)
    simpa only [metaplecticCubeProduct,←he] using hb.trans hevb.symm

lemma metaplectic_cube_pair_weight (S : Finset (Eisenstein × Eisenstein))
    (hS : ∀ du ∈ S, primary du.1 ∧ primary du.2) {V : ℝ} (hV : 0 ≤ V)
    (hsize : ∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) :
    (∑ du ∈ S, norm du.1) ≤
      18*V*(∑' d : Eisenstein, norm d^(-2:ℝ)) := by
  let D := S.image Prod.fst
  have hrow (d : Eisenstein) (hd : d ∈ D) :
      (∑ du ∈ S with du.1 = d, norm du.1) ≤ 18*V*norm d^(-2:ℝ) := by
    obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hd
    have hdp : 0 < norm du.1 := norm_pos_of_ne_zero (primary_ne_zero (hS du hdu).1)
    let T := S.filter (fun ev => ev.1 = du.1)
    have hcard : (T.card:ℝ) ≤ 18*(V/norm du.1^3) := by
      have hcardN : T.card ≤ (nonzeroNormBall (V/norm du.1^3)).card := by
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro ev hev
          obtain ⟨hev,he⟩ := Finset.mem_filter.mp hev
          apply mem_nonzeroNormBall.mpr
          refine ⟨(le_div_iff₀ (pow_pos hdp 3)).mpr ?_,primary_ne_zero (hS ev hev).2⟩
          have hs := hsize ev hev
          rw [metaplecticCubeProduct_norm,he] at hs
          exact hs
        · intro ev hev ew hew he
          exact Prod.ext ((Finset.mem_filter.mp hev).2.trans (Finset.mem_filter.mp hew).2.symm) he
      exact (Nat.cast_le.mpr hcardN).trans (nonzeroNormBall_card_le (by positivity))
    have hsum : (∑ ev ∈ T, norm ev.1) = (T.card:ℝ)*norm du.1 := by
      calc
        _ = ∑ _ev ∈ T, norm du.1 := Finset.sum_congr rfl (fun ev hev => congrArg norm (Finset.mem_filter.mp hev).2)
        _ = _ := by simp
    change (∑ ev ∈ T, norm ev.1) ≤ _
    rw [hsum]
    apply (mul_le_mul_of_nonneg_right hcard hdp.le).trans_eq
    rw [Real.rpow_neg hdp.le,Real.rpow_two]
    field_simp [hdp.ne']
  calc
    _ = ∑ d ∈ D, ∑ du ∈ S with du.1 = d, norm du.1 :=
      (Finset.sum_fiberwise_of_maps_to (fun du hdu => Finset.mem_image_of_mem _ hdu) _).symm
    _ ≤ ∑ d ∈ D, 18*V*norm d^(-2:ℝ) := Finset.sum_le_sum hrow
    _ = 18*V*(∑ d ∈ D, norm d^(-2:ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_eisenstein_norm_rpow (show (1:ℝ) < 2 by norm_num)).sum_le_tsum D
        (fun d _ => Real.rpow_nonneg (norm_nonneg d) _)) (by positivity)

/-- The coefficient energy after collecting actual cube products. -/
theorem metaplectic_cube_energy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Eisenstein × Eisenstein)),
      (∀ du ∈ S, primary du.1 ∧ primary du.2) →
      ∀ (w : Eisenstein × Eisenstein → ℂ) (V M : ℝ), 1 ≤ V → 0 ≤ M →
      (∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) →
      (∀ du ∈ S, ‖w du‖^2 ≤ norm du.1*M^2) →
      (∑ b ∈ S.image metaplecticCubeProduct, ‖metaplecticCubeCoefficient S w b‖^2) ≤
        C*V^(1+ε)*M^2 := by
  obtain ⟨D,hD,hdiv⟩ := primary_divisor_card_small_power hε
  let B := 18*(∑' d : Eisenstein, norm d^(-2:ℝ))
  have hB : 0 ≤ B := mul_nonneg (by norm_num)
    (tsum_nonneg (fun d => Real.rpow_nonneg (norm_nonneg d) _))
  refine ⟨D*(B+1),mul_pos hD (by linarith),?_⟩
  intro S hS w V M hV _hM hsize hw
  have hrow (b : Eisenstein) (hb : b ∈ S.image metaplecticCubeProduct) :
      ‖metaplecticCubeCoefficient S w b‖^2 ≤
        D*V^ε*(∑ du ∈ S with metaplecticCubeProduct du = b, ‖w du‖^2) := by
    have hCS := complex_bilinear_rows_sq (S.filter (fun du => metaplecticCubeProduct du = b))
      (fun _ => (1:ℂ)) w
    simp only [one_mul,norm_one,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hCS
    apply hCS.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    obtain ⟨du,hdu,rfl⟩ := Finset.mem_image.mp hb
    have hb0 : metaplecticCubeProduct du ≠ 0 :=
      mul_ne_zero (primary_ne_zero (hS du hdu).2) (pow_ne_zero 3 (primary_ne_zero (hS du hdu).1))
    exact (Nat.cast_le.mpr (metaplectic_cube_fiber_card S hS)).trans
      ((hdiv (S.image Prod.fst) (fun d hd => by
        obtain ⟨ev,hev,rfl⟩ := Finset.mem_image.mp hd
        exact (hS ev hev).1) _ hb0).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (hsize du hdu) hε.le) hD.le))
  have henergy : (∑ du ∈ S, ‖w du‖^2) ≤ B*V*M^2 := by
    calc
      _ ≤ ∑ du ∈ S, norm du.1*M^2 := Finset.sum_le_sum hw
      _ = (∑ du ∈ S, norm du.1)*M^2 := (Finset.sum_mul _ _ _).symm
      _ ≤ (18*V*(∑' d : Eisenstein, norm d^(-2:ℝ)))*M^2 :=
        mul_le_mul_of_nonneg_right (metaplectic_cube_pair_weight S hS (by linarith) hsize) (sq_nonneg M)
      _ = _ := by dsimp [B]; ring
  calc
    _ ≤ ∑ b ∈ S.image metaplecticCubeProduct,
        D*V^ε*(∑ du ∈ S with metaplecticCubeProduct du = b, ‖w du‖^2) := Finset.sum_le_sum hrow
    _ = D*V^ε*(∑ du ∈ S, ‖w du‖^2) := by
      rw [←Finset.mul_sum,Finset.sum_fiberwise_of_maps_to (fun du hdu => Finset.mem_image_of_mem _ hdu)]
    _ ≤ D*V^ε*(B*V*M^2) := mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = D*B*V^(1+ε)*M^2 := by rw [Real.rpow_add (by linarith : 0 < V),Real.rpow_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hD.le)
      (Real.rpow_nonneg (by linarith) _)) (sq_nonneg M)

/-- The literal primal summand before its norm-phase, as in the
published completed sum. -/
def metaplecticPrimalCoefficient (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ)
    (X : ℝ) (du : Eisenstein × Eisenstein) : ℂ :=
  if IsCoprime du.1 r then
    (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*
      theta ℓ (r*metaplecticCubeProduct du)*W (norm (metaplecticCubeProduct du)/X)
  else 0

lemma metaplecticPrimalCoefficient_sq_le {r : Eisenstein} (hr : primary r)
    (ℓ : ℤ) (W : ℝ → ℂ) (X : ℝ) {du : Eisenstein × Eisenstein}
    (hd : primary du.1) (hu : primary du.2) {M : ℝ} (_hM : 0 ≤ M)
    (hW : ‖W (norm (metaplecticCubeProduct du)/X)‖ ≤ M) :
    ‖metaplecticPrimalCoefficient r ℓ W X du‖^2 ≤ norm du.1*M^2 := by
  have hg : ‖gauss (r*du.2)‖ ≤ 1 := by
    rw [norm_gauss (primary_mul hr hu)]
    split_ifs <;> norm_num
  have ht : ‖theta ℓ (r*metaplecticCubeProduct du)‖ = 1 :=
    norm_theta (primary_ne_zero (primary_mul hr
      (primary_mul hu (by simpa only [pow_succ,pow_zero,one_mul] using primary_mul (primary_mul hd hd) hd)))) ℓ
  unfold metaplecticPrimalCoefficient
  split_ifs
  · have hh : ‖(Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*
        theta ℓ (r*metaplecticCubeProduct du)*W (norm (metaplecticCubeProduct du)/X)‖ ≤
        Real.sqrt (norm du.1)*M := by
      rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _),ht,mul_one]
      calc
        _ ≤ (Real.sqrt (norm du.1)*1)*M := by gcongr
        _ = _ := by ring
    exact (pow_le_pow_left₀ (_root_.norm_nonneg _) hh 2).trans_eq (by
      rw [mul_pow,Real.sq_sqrt (norm_nonneg _)])
  · rw [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]
    exact mul_nonneg (norm_nonneg _) (sq_nonneg M)

/-- No coefficient-energy hypothesis remains for the actual completed
Gauss summand: its modulus bound is supplied by the Gauss and angular
identities. -/
theorem metaplectic_primal_energy {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Eisenstein × Eisenstein)),
      (∀ du ∈ S, primary du.1 ∧ primary du.2) →
      ∀ (r : Eisenstein), primary r → ∀ (ℓ : ℤ) (W : ℝ → ℂ) (X V M : ℝ),
      1 ≤ V → 0 ≤ M → (∀ du ∈ S, norm (metaplecticCubeProduct du) ≤ V) →
      (∀ du ∈ S, ‖W (norm (metaplecticCubeProduct du)/X)‖ ≤ M) →
      (∑ b ∈ S.image metaplecticCubeProduct,
        ‖metaplecticCubeCoefficient S (metaplecticPrimalCoefficient r ℓ W X) b‖^2) ≤
          C*V^(1+ε)*M^2 := by
  obtain ⟨C,hC,hE⟩ := metaplectic_cube_energy hε
  refine ⟨C,hC,?_⟩
  intro S hS r hr ℓ W X V M hV hM hsize hW
  exact hE S hS _ V M hV hM hsize (fun du hdu =>
    metaplecticPrimalCoefficient_sq_le hr ℓ W X (hS du hdu).1 (hS du hdu).2 hM (hW du hdu))

end CubicFirstMoment

end

end OAI
