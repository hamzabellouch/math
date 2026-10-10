import OAI.Probability.BenjaminiSchramm.TiltedMomentBridge
import OAI.Probability.CriticalPercolation.Modular.ModularIncidence

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def modularLogHeight (x y : V) : ℝ := Real.log (G.modularRatio y x)

def modularSlab (x : V) (a b : ℝ) : Set V :=
  {y | a ≤ G.modularLogHeight x y ∧ G.modularLogHeight x y ≤ b}

@[simp] lemma modularLogHeight_self (x : V) : G.modularLogHeight x x = 0 := by
  simp only [modularLogHeight,G.modularRatio_self,Real.log_one]

lemma modularLogHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x v y : V) : G.modularLogHeight x y = G.modularLogHeight x v + G.modularLogHeight v y := by
  unfold modularLogHeight
  rw [← Real.log_mul (G.modularRatio_pos hc hl v x).ne' (G.modularRatio_pos hc hl y v).ne']
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

lemma modularLogHeight_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : G.modularLogHeight y x = -G.modularLogHeight x y := by
  have h := G.modularLogHeight_change_base hc hl x y x
  rw [G.modularLogHeight_self] at h
  linarith

lemma Aut.modularLogHeight (φ : G.Aut) (x y : V) :
    G.modularLogHeight (φ.vertex x) (φ.vertex y) = G.modularLogHeight x y := by
  simp only [CriticalPercolation.BondGraph.modularLogHeight,Aut.modularRatio]

lemma modularSlab_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x v : V) (a b : ℝ) : G.modularSlab x a b =
      G.modularSlab v (a - G.modularLogHeight x v) (b - G.modularLogHeight x v) := by
  ext y
  change (a ≤ G.modularLogHeight x y ∧ G.modularLogHeight x y ≤ b) ↔ _
  rw [G.modularLogHeight_change_base hc hl x v y]
  change (a ≤ G.modularLogHeight x v + G.modularLogHeight v y ∧
    G.modularLogHeight x v + G.modularLogHeight v y ≤ b) ↔
      (a - G.modularLogHeight x v ≤ G.modularLogHeight v y ∧
        G.modularLogHeight v y ≤ b - G.modularLogHeight x v)
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

lemma modularSlab_mono (x : V) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    G.modularSlab x a b ⊆ G.modularSlab x a' b' :=
  fun _ h => ⟨ha.trans h.1,h.2.trans hb⟩

lemma modularLogHeight_eq_log_weight (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : G.modularLogHeight x y = Real.log (G.stabilizerWeight x y).toReal := by
  rw [stabilizerWeight,ENNReal.toReal_ofReal (G.modularRatio_pos hc hl y x).le]
  rfl

lemma modularLogHeight_le_log_ball_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (x y : V)
    (hxy : y ∈ G.vertexBall x 1) (hyx : x ∈ G.vertexBall y 1) :
    G.modularLogHeight x y ≤ Real.log (K : ℝ) := by
  rw [G.modularLogHeight_eq_log_weight hc hl]
  apply Real.log_le_log (ENNReal.toReal_pos (G.stabilizerWeight_pos hc hl x y).ne'
    (G.stabilizerWeight_ne_top x y))
  simpa only [ENNReal.toReal_natCast,ENNReal.coe_toReal,NNReal.coe_natCast] using ENNReal.toReal_mono ENNReal.coe_ne_top
    (G.stabilizerWeight_le_ball_bound hc hl K hK hxy hyx)

lemma modularLogHeight_edge_jump (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (o x y : V) (e : E)
    (hx : x ∈ G.ends e) (hy : y ∈ G.ends e) :
    |G.modularLogHeight o y - G.modularLogHeight o x| ≤ Real.log (K : ℝ) := by
  rw [G.modularLogHeight_change_base hc hl o x y,add_sub_cancel_left,abs_le]
  constructor
  · have h := G.modularLogHeight_le_log_ball_bound hc hl K hK y x
      (G.common_bond_ball_one hy hx) (G.common_bond_ball_one hx hy)
    rw [G.modularLogHeight_reverse hc hl] at h
    linarith
  · exact G.modularLogHeight_le_log_ball_bound hc hl K hK x y
      (G.common_bond_ball_one hx hy) (G.common_bond_ball_one hy hx)

end CriticalPercolation.BondGraph

end

end OAI
