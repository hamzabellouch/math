import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszContourError
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszLeftBound
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszHorizontalBound
import OAI.NumberTheory.JointDickman.Analysis.PerronScaleGeometry
import OAI.NumberTheory.JointDickman.Analysis.SquarefreeRieszPerronLocal

namespace OAI

/-! # A quantitative global error at the chosen Perron scale -/
namespace JointDickman
open Complex Filter Set
open scoped Topology

theorem squarefreeRiesz_scale_error {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    ∃ A C D : ℝ, 0 < A ∧ 0 < C ∧ 0 < D ∧
      ∀ᶠ q : ℝ in atTop,
        |(VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) (1/q^10)).re -
          squarefreeRieszLocalHankel z (perronScaleWidth A q) (q^10)| ≤
        C*((D/perronScaleWidth A q)^z*Real.exp (-(q^10*perronScaleWidth A q)) +
          (Real.exp q/2)^(-1/2:ℝ)) := by
  obtain ⟨A₀,hA₀,hA₀4,hlog⟩ := zeta_rectangle_log_below
  obtain ⟨A₁,D,G,hA₁,hD,hG,hleft⟩ := squarefreeRiesz_left_bound hz hz1.le
  obtain ⟨A₂,E,hA₂,hE,hhor⟩ := squarefreeRiesz_horizontal_bound hz hz1.le
  obtain ⟨F,hF,htail⟩ := squarefreeNormalizedPerron_truncation_bound hz hz1.le
  obtain ⟨r,hr,herror⟩ := squarefreeRiesz_contour_error_le
  let A := min A₀ (min A₁ A₂)
  have hA : 0 < A := lt_min hA₀ (lt_min hA₁.1 hA₂.1)
  have hAA₀ : A ≤ A₀ := min_le_left _ _
  have hAA₁ : A ≤ A₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hAA₂ : A ≤ A₂ := (min_le_right _ _).trans (min_le_right _ _)
  let C := F*Real.exp 1 + (1/(2*Real.pi))*(5*G*Real.pi+2*E*Real.exp 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨A,C,D,hA,hC,hD,?_⟩
  filter_upwards [eventually_ge_atTop (max 8 (2048/A)),
    (perronScaleWidth_tendsto_zero hA).eventually (gt_mem_nhds hr)] with q hq hqr
  have hq8 : 8 ≤ q := (le_max_left _ _).trans hq
  have hqA : 2048/A ≤ q := (le_max_right _ _).trans hq
  have hq0 : 0 < q := by linarith
  let η := perronScaleWidth A q
  let c : ℝ := 1/q^10
  let T := Real.exp q/2
  have hη : 0 < η := perronScaleWidth_pos hA
  have hη4 : 4*η ≤ 1/4 := (perronScaleWidth_four_le hA (by linarith)).trans (hAA₀.trans hA₀4)
  have hη1 : η ≤ 1/4 := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hcη : c ≤ η := perronScale_right_le_width hA (by linarith) hqA
  have hc1 : c ≤ 1 := by linarith
  have hT : 3 < T := perronScale_height_gt_three hq8
  have hT4 : 4 ≤ T := by dsimp [T]; linarith [Real.add_one_le_exp q]
  have hL : 0 ≤ q^10 := pow_nonneg hq0.le _
  have hLc : q^10*c = 1 := by dsimp [c]; field_simp
  have hηlog := perronScaleWidth_le_log_height hA hq8
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hηA₁ : η ≤ A₁/Real.log T := hηlog.trans (div_le_div_of_nonneg_right hAA₁ hlogT.le)
  have hηA₂ : η ≤ A₂/Real.log T := hηlog.trans (div_le_div_of_nonneg_right hAA₂ hlogT.le)
  obtain ⟨f,hf,hf1,he⟩ := hlog A hA hAA₀ (Real.exp q) (Real.exp_pos q)
  have hrect : zetaOpenRectangle (4*η) (2*T) =
      zetaOpenRectangle (zetaContourWidth A (Real.exp q)) (Real.exp q) := by
    dsimp [η,T,perronScaleWidth]
    congr 1 <;> ring
  rw [←hrect] at hf he
  have hbranch (u t : ℝ) (hu : u ∈ Icc (-η) c) (ht : |t| ≤ T) :
      exp (f (1+((u:ℂ)+(t:ℂ)*I))) = zetaPoleFactor (1+((u:ℂ)+(t:ℂ)*I)) := by
    apply he
    apply perron_inner_contour_mem hη hη1 hcη (by linarith : 0 < T)
    · simpa using hu
    · simpa using ht
  have hl := hleft η T (q^10) f hη hη1 hT4 hηA₁
    (fun t ht => hbranch (-η) t ⟨le_rfl,by linarith⟩ (abs_le.mpr ht))
  have hhor' (ε : ℝ) (hε : |ε| = 1) :=
    hhor η c T (q^10) ε f hη.le hη1 hc.le hc1 hT hL hηA₂ hε
      (fun u hu => hbranch u (ε*T) hu (by rw [abs_mul,hε,abs_of_pos (by linarith : 0 < T),one_mul]))
  have hhPos := hhor' 1 (by norm_num)
  have hhNeg := hhor' (-1) (by norm_num)
  simp only [one_mul,neg_one_mul] at hhPos hhNeg
  have ht := htail (q^10) c T hc hc1 hT
  have he' := herror (L := q^10) hz hz1 (by linarith : 0 < 4*η) hη4
    (by simpa using hqr) hc (by simpa using hcη) (by linarith : 1 < T) hf hf1 he
  simp only [show 4*η/4 = η by ring,show -(4*η)/4 = -η by ring] at he'
  change |(VerticalIntegral' (squarefreeNormalizedPerron z (q^10)) c).re -
    squarefreeRieszLocalHankel z η (q^10)| ≤ _
  have hhalf : T^(-3/2:ℝ) ≤ T^(-1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hlen : η+c ≤ 1 := by linarith
  have hhorbound : E*Real.exp (q^10*c)*T^(-3/2:ℝ)*(η+c) ≤
      E*Real.exp 1*T^(-1/2:ℝ) := by
    rw [hLc]
    calc
      _ ≤ E*Real.exp 1*T^(-3/2:ℝ)*1 :=
        mul_le_mul_of_nonneg_left hlen (by positivity)
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ E*Real.exp 1)
  rw [hLc] at ht
  calc
    _ ≤ F*Real.exp 1*T^(-1/2:ℝ) + (1/(2*Real.pi)) *
        ((5*G*(D/η)^z*Real.exp (-(q^10*η)))*Real.pi +
          E*Real.exp 1*T^(-1/2:ℝ)+E*Real.exp 1*T^(-1/2:ℝ)) := by
      exact he'.trans (add_le_add ht (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hl (hhPos.trans hhorbound)) (hhNeg.trans hhorbound)) (by positivity)))
    _ ≤ C*((D/η)^z*Real.exp (-(q^10*η)) + T^(-1/2:ℝ)) := by
      dsimp [C]
      have hp : 0 ≤ (D/η)^z*Real.exp (-(q^10*η)) := by positivity
      have htpos : 0 ≤ T^(-1/2:ℝ) := by positivity
      have hcross₁ : 0 ≤ F*Real.exp 1*((D/η)^z*Real.exp (-(q^10*η))) := by positivity
      have hcross₂ : 0 ≤ (1/(2*Real.pi))*(5*G*Real.pi)*T^(-1/2:ℝ) := by positivity
      have hcross₃ : 0 ≤ (1/(2*Real.pi))*(2*E*Real.exp 1)*((D/η)^z*Real.exp (-(q^10*η))) := by positivity
      nlinarith

end JointDickman

end OAI
