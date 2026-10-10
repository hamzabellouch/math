import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.AmbientGridCell3

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set Metric

lemma exists_far_separation_powerND (d : ℕ) :
    ∃ k : ℕ, 1000*(d+1:ℝ)<(2:ℝ)^k ∧ (2:ℝ)^k<4000*(d+1:ℝ) := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near (x := 1000*(d+1:ℝ)) (y := (2:ℝ))
    (by have hd : (0:ℝ)≤d := Nat.cast_nonneg d; linarith) (by norm_num)
  refine ⟨n+1,hn',?_⟩
  rw [pow_succ]
  nlinarith

def farSeparatedGridND {d : ℕ} (b : ℕ) (K : ℝ) (X Y : Fin d → ℤ) : Prop :=
  K/(8*(2:ℝ)^b)≤dist (ambientGridCenter b X) (ambientGridCenter b Y) ∧
    dist (ambientGridCenter b X) (ambientGridCenter b Y)≤4*K/(2:ℝ)^b

theorem farSeparatedGridND_of_lengths {d b : ℕ} {K : ℝ}
    (hK : 16*(d+1:ℝ)≤K) {X Y : Fin d → ℤ} {x y : EuclideanSpace ℝ (Fin d)}
    (hx : x∈ambientGridCell b X) (hy : y∈ambientGridCell b Y)
    (hlo : K/(4*(2:ℝ)^b)≤dist x y) (hhi : dist x y≤K/(2:ℝ)^b) :
    farSeparatedGridND b K X Y := by
  have htp : 0<(2:ℝ)^b := by positivity
  have hcx := ambientGridCell_dist_le hx (ambientGridCenter_mem b X)
  have hcy := ambientGridCell_dist_le hy (ambientGridCenter_mem b Y)
  have hxy := dist_triangle4 x (ambientGridCenter b X) (ambientGridCenter b Y) y
  have hcc := dist_triangle4 (ambientGridCenter b X) x y (ambientGridCenter b Y)
  rw [dist_comm x (ambientGridCenter b X)] at hxy
  rw [dist_comm y (ambientGridCenter b Y)] at hcc
  have hscale := div_le_div_of_nonneg_right hK htp.le
  have hscale' : 16*((d+1:ℝ)/(2:ℝ)^b)≤K/(2:ℝ)^b := by simpa only [mul_div_assoc] using hscale
  have he₁ : K/(4*(2:ℝ)^b)=(K/(2:ℝ)^b)/4 := by ring
  have he₂ : K/(8*(2:ℝ)^b)=(K/(2:ℝ)^b)/8 := by ring
  have he₃ : 4*K/(2:ℝ)^b=4*(K/(2:ℝ)^b) := by ring
  dsimp [farSeparatedGridND]
  rw [he₂,he₃]
  rw [he₁] at hlo
  constructor <;> linarith

theorem farSeparatedGridND_partner_card {d : ℕ} (b : ℕ) {K : ℝ} (hK : 0≤K)
    (X : Fin d → ℤ) (P : Finset (Fin d → ℤ))
    (hP : ∀ Y∈P, farSeparatedGridND b K X Y) :
    (P.card:ℝ)≤(8*K+5)^d := by
  have hh := ambientGridCenter_ball_card b P (ambientGridCenter b X)
    (r := 4*K/(2:ℝ)^b) (by positivity) (fun Y hY => by
      rw [dist_comm]; exact (hP Y hY).2)
  convert hh using 1
  congr 1
  field_simp; ring

theorem exists_far_common_depthND {D₁ D₂ K : ℝ} (hD₁ : 0<D₁) (hD₂ : 0<D₂)
    (hcomp : max D₁ D₂≤2*min D₁ D₂) (hsize : max D₁ D₂≤K) :
    ∃ b : ℕ, K/(4*(2:ℝ)^b)≤D₁ ∧ D₁≤K/(2:ℝ)^b ∧
      K/(4*(2:ℝ)^b)≤D₂ ∧ D₂≤K/(2:ℝ)^b ∧
      K/(2*(2:ℝ)^b)< max D₁ D₂ := by
  have hD : 0< max D₁ D₂ := (lt_min hD₁ hD₂).trans_le min_le_max
  have hK : 0<K := hD.trans_le hsize
  obtain ⟨b,hb,hb'⟩ := exists_nat_pow_near
    ((one_le_div hD).mpr hsize) (by norm_num : (1:ℝ)<2)
  have hp : 0<(2:ℝ)^b := by positivity
  have hu : max D₁ D₂≤K/(2:ℝ)^b := by
    apply (le_div_iff₀ hp).mpr
    have hh := (le_div_iff₀ hD).mp hb
    nlinarith
  have hl : K/(2*(2:ℝ)^b)< max D₁ D₂ := by
    apply (div_lt_iff₀ (by positivity : 0<2*(2:ℝ)^b)).mpr
    rw [pow_succ] at hb'
    have hh := (div_lt_iff₀ hD).mp hb'
    nlinarith
  have hm : K/(4*(2:ℝ)^b)≤ min D₁ D₂ := by
    have he : K/(2*(2:ℝ)^b)=2*(K/(4*(2:ℝ)^b)) := by ring
    rw [he] at hl
    linarith
  exact ⟨b,hm.trans (min_le_left _ _),(le_max_left _ _).trans hu,
    hm.trans (min_le_right _ _),(le_max_right _ _).trans hu,hl⟩

lemma far_common_depth_strictND {d a b : ℕ} {D K : ℝ}
    (hK : 16*(d+1:ℝ)≤K) (hl : K/(2*(2:ℝ)^b)<D)
    (hu : D≤(d+1:ℝ)/(2:ℝ)^a) : a<b := by
  by_contra h
  have hba : b≤a := by omega
  have hpow : (2:ℝ)^b≤(2:ℝ)^a := pow_le_pow_right₀ (by norm_num) hba
  have hKp : 0<K := by have hd : (0:ℝ)≤d := Nat.cast_nonneg d; linarith
  have hscale : K/(2*(2:ℝ)^a)≤K/(2*(2:ℝ)^b) :=
    div_le_div_of_nonneg_left hKp.le (by positivity) (by gcongr)
  have hbad : K/(2*(2:ℝ)^a)<(d+1:ℝ)/(2:ℝ)^a := hscale.trans_lt (hl.trans_le hu)
  have he : K/(2*(2:ℝ)^a)=(K/2)/(2:ℝ)^a := by ring
  rw [he] at hbad
  have hh := (div_lt_div_iff_of_pos_right (by positivity : 0<(2:ℝ)^a)).mp hbad
  linarith

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
