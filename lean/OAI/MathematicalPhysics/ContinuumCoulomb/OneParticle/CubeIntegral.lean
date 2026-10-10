import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.SlabCoordinates

namespace OAI

/-! The normalized tensor cell integral is the ordinary Euclidean volume
integral on the translated cube, with no change of volume convention. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def cubeTripleBox (b : Position) (h : ℝ) : Set SlabTriple :=
  Set.Icc (b 0-h/2) (b 0+h/2) ×ˢ
    (Set.Icc (b 1-h/2) (b 1+h/2) ×ˢ Set.Icc (b 2-h/2) (b 2+h/2))

theorem cubeTripleBox_measurable (b : Position) (h : ℝ) :
    MeasurableSet (cubeTripleBox b h) :=
  measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)

theorem cubeTripleBox_preimage (b : Position) (h : ℝ) :
    slabTripleEquiv ⁻¹' cubeTripleBox b h = positionCube b h := by
  ext x
  simp only [Set.mem_preimage,cubeTripleBox,slabTripleEquiv_apply,Set.mem_prod,
    Set.mem_Icc,mem_positionCube]
  constructor
  · rintro ⟨h0,h1,h2⟩ i
    fin_cases i
    · change |x 0-b 0| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h0.1],by linarith [h0.2]⟩
    · change |x 1-b 1| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h1.1],by linarith [h1.2]⟩
    · change |x 2-b 2| ≤ h/2
      exact abs_le.mpr ⟨by linarith [h2.1],by linarith [h2.2]⟩
  · intro hx
    have h0 := abs_le.mp (hx 0)
    have h1 := abs_le.mp (hx 1)
    have h2 := abs_le.mp (hx 2)
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,
      ⟨by linarith,by linarith⟩⟩

theorem cube_setIntegral_triple (b : Position) (h : ℝ) (f : Position → ℝ) :
    (∫ x in positionCube b h, f x) =
      ∫ p in cubeTripleBox b h, f (slabTripleEquiv.symm p) := by
  have hm := slabTripleEquiv_measurePreserving.restrict_preimage (cubeTripleBox_measurable b h)
  rw [cubeTripleBox_preimage] at hm
  simpa only [Function.comp_apply,MeasurableEquiv.symm_apply_apply] using
    hm.integral_comp' (f ∘ slabTripleEquiv.symm)

theorem centered_interval_integral (c h : ℝ) (f : ℝ → ℝ) :
    (h/2)*(∫ t : ℝ in (-1)..1, f (c+h/2*t)) =
      ∫ t : ℝ in (c-h/2)..(c+h/2), f t := by
  have he := intervalIntegral.smul_integral_comp_add_mul
    (f := f) (a := (-1:ℝ)) (b := 1) (h/2) c
  simpa only [smul_eq_mul,mul_neg_one,mul_one,← sub_eq_add_neg] using he

theorem centered_triple_integral (c₀ c₁ c₂ h : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    (h/2)^3*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
      f (c₀+h/2*x) (c₁+h/2*y) (c₂+h/2*z)) =
      ∫ x : ℝ in (c₀-h/2)..(c₀+h/2),
        ∫ y : ℝ in (c₁-h/2)..(c₁+h/2),
          ∫ z : ℝ in (c₂-h/2)..(c₂+h/2), f x y z := by
  let d := h/2
  have hz (x y : ℝ) : d*(∫ z : ℝ in (-1)..1, f x y (c₂+d*z)) =
      ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z := centered_interval_integral c₂ h (f x y)
  have hy (x : ℝ) : d^2*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (-1)..1,
      f x (c₁+d*y) (c₂+d*z)) =
      ∫ y : ℝ in (c₁-d)..(c₁+d), ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z := by
    calc
      _ = d*(∫ y : ℝ in (-1)..1, d*(∫ z : ℝ in (-1)..1, f x (c₁+d*y) (c₂+d*z))) := by
        rw [intervalIntegral.integral_const_mul]
        ring
      _ = d*(∫ y : ℝ in (-1)..1, ∫ z : ℝ in (c₂-d)..(c₂+d), f x (c₁+d*y) z) := by
        simp_rw [hz]
      _ = _ := centered_interval_integral c₁ h (fun y => ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z)
  change d^3*_ = _
  calc
    _ = d*(∫ x : ℝ in (-1)..1, d^2*(∫ y : ℝ in (-1)..1,
        ∫ z : ℝ in (-1)..1, f (c₀+d*x) (c₁+d*y) (c₂+d*z))) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = d*(∫ x : ℝ in (-1)..1, ∫ y : ℝ in (c₁-d)..(c₁+d),
        ∫ z : ℝ in (c₂-d)..(c₂+d), f (c₀+d*x) y z) := by simp_rw [hy]
    _ = _ := centered_interval_integral c₀ h
      (fun x => ∫ y : ℝ in (c₁-d)..(c₁+d), ∫ z : ℝ in (c₂-d)..(c₂+d), f x y z)

theorem positionCellIntegral_eq_setIntegral (b : Position) {h : ℝ} (hh : 0 ≤ h)
    (f : Position → ℝ) (hf : IntegrableOn f (positionCube b h)) :
    positionCellIntegral b h f = ∫ x in positionCube b h, f x := by
  let F : SlabTriple → ℝ := fun p => f (slabTripleEquiv.symm p)
  have hm := slabTripleEquiv_measurePreserving.restrict_preimage (cubeTripleBox_measurable b h)
  rw [cubeTripleBox_preimage] at hm
  have hF : IntegrableOn F (cubeTripleBox b h) :=
    (hm.integrable_comp_emb slabTripleEquiv.measurableEmbedding).mp
      (by simpa only [IntegrableOn,F,Function.comp_def,MeasurableEquiv.symm_apply_apply] using hf)
  have ht : (∫ p in cubeTripleBox b h, F p) =
      ∫ x in Set.Icc (b 0-h/2) (b 0+h/2),
        ∫ y in Set.Icc (b 1-h/2) (b 1+h/2),
          ∫ z in Set.Icc (b 2-h/2) (b 2+h/2), F (x,y,z) := by
    rw [cubeTripleBox,Measure.volume_eq_prod] at hF ⊢
    rw [setIntegral_prod _ hF]
    apply integral_congr_ae
    have hFa := hF
    rw [IntegrableOn,← Measure.prod_restrict] at hFa
    filter_upwards [hFa.prod_right_ae] with x hx
    exact setIntegral_prod _ hx
  rw [cube_setIntegral_triple,ht]
  have hi (i : Fin 3) : b i-h/2 ≤ b i+h/2 := by linarith
  have he (x y z : ℝ) : cubePoint b (h/2) x y z =
      slabTripleEquiv.symm (b 0+h/2*x,b 1+h/2*y,b 2+h/2*z) := by
    rw [slabTripleEquiv_symm_apply]
    ext i
    fin_cases i <;> simp [cubePoint] <;> ring
  unfold positionCellIntegral
  simp_rw [he]
  rw [centered_triple_integral (b 0) (b 1) (b 2) h
    (fun x y z => f (slabTripleEquiv.symm (x,y,z)))]
  simp_rw [intervalIntegral.integral_of_le (hi _),← integral_Icc_eq_integral_Ioc]
  rfl

end ContinuumCoulomb

end

end OAI
