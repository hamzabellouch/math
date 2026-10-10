import OAI.Probability.InvariantIsing.Magnetic.MagneticRoundedCount

namespace OAI

/-! The real magnetization associated with an attainable integer count. -/
noncomputable section
namespace InvariantIsing

def spinCountMagnetization (G k : ℕ) : ℝ := if G=0 then 0 else 2*(k:ℝ)/G-1

lemma spinCountMagnetization_bounds {G k : ℕ} (hk : k≤G) :
    |spinCountMagnetization G k|≤1 := by
  by_cases hG : G=0
  · simp [spinCountMagnetization,hG]
  · have hp : (0:ℝ)<G := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hG)
    have hk' : (k:ℝ)≤G := Nat.cast_le.mpr hk
    simp only [spinCountMagnetization,ite_eq_right hG]
    apply abs_le.mpr
    constructor
    · have : (0:ℝ)≤2*k/G := by positivity
      linarith
    · have : 2*(k:ℝ)/G≤2 := (div_le_iff₀ hp).mpr (by linarith)
      linarith

lemma spinCountMagnetization_count {G k : ℕ} (hk : k≤G) :
    (k:ℝ)=(G:ℝ)*((1+spinCountMagnetization G k)/2) := by
  by_cases hG : G=0
  · have : k=0 := by omega
    simp [spinCountMagnetization,hG,this]
  · simp only [spinCountMagnetization,ite_eq_right hG]
    have hn : (G:ℝ)≠0 := Nat.cast_ne_zero.mpr hG
    field_simp
    ring

lemma rounded_count_distance {G k : ℕ} (hk : k≤G) {q δ : ℝ}
    (hq : |q|≤1) (hd : |spinCountMagnetization G k-q|≤δ) :
    |(k:ℝ)-(magneticRoundedCount G q:ℝ)|≤(G:ℝ)*δ/2+1 := by
  have hx : 0≤(G:ℝ)*((1+q)/2) :=
    mul_nonneg (Nat.cast_nonneg _) (by linarith [(abs_le.mp hq).1])
  have hl := Nat.floor_le hx
  have hu := Nat.lt_floor_add_one ((G:ℝ)*((1+q)/2))
  have ha : |(G:ℝ)*((1+q)/2)-(magneticRoundedCount G q:ℝ)|≤1 := by
    apply abs_le.mpr
    dsimp only [magneticRoundedCount]
    constructor <;> linarith
  have he : (k:ℝ)-(G:ℝ)*((1+q)/2)=
      (G:ℝ)/2*(spinCountMagnetization G k-q) := by
    rw [spinCountMagnetization_count hk]
    ring
  calc
    _ ≤ |(k:ℝ)-(G:ℝ)*((1+q)/2)|+
        |(G:ℝ)*((1+q)/2)-(magneticRoundedCount G q:ℝ)| := abs_sub_le _ _ _
    _ ≤ (G:ℝ)/2*δ+1 := by
      rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤(G:ℝ)/2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hd (by positivity)) ha
    _ = _ := by ring

end InvariantIsing

end

end OAI
