import Mathlib
import OAI.Probability.CriticalPercolation.Gluing.CorridorNormalization
import OAI.Probability.CriticalPercolation.Gluing.MoveExit
import OAI.Probability.CriticalPercolation.Gluing.MoveWitness

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma signed_div_abs (b : Bool) (x U : ℝ) (hU : 0<U) :
    |Corridor.sign b*x/U|=|x|/U := by
  rw [abs_div,abs_mul,Corridor.sign_abs,one_mul,abs_of_pos hU]

lemma signed_exit_error (b : Bool) (x U D : ℝ) (hU : 0<U)
    (hx : U≤Corridor.sign b*x) (hx' : Corridor.sign b*x≤U+D) :
    |Corridor.sign b*x/U-1|≤D/U := by
  rw [abs_of_nonneg (by exact sub_nonneg.mpr ((le_div_iff₀ hU).mpr (by simpa using hx)))]
  exact (sub_le_iff_le_add).mpr ((div_le_iff₀ hU).mpr (by
    simpa only [add_mul,div_mul_cancel₀ _ hU.ne',one_mul,add_comm] using hx'))

def stripTime (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U+Corridor.sign b*v x/Q

def stripHeight (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U-Corridor.sign b*v x/Q

lemma strip_coordinate_bounds (u v : V → ℝ) (U Q : ℝ) (a b : Bool)
    (hU : 0<U) (hQ : 0<Q) (x : V) :
    |stripTime u v U Q a b x|≤|u x|/U+|v x|/Q ∧
    |stripHeight u v U Q a b x|≤|u x|/U+|v x|/Q := by
  constructor
  · exact (abs_add_le _ _).trans_eq (by rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ])
  · exact (abs_sub _ _).trans_eq (by rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ])

lemma strip_coordinate_increments (u v : V → ℝ) (U Q D : ℝ) (a b : Bool)
    (hU : 0<U) (hQ : 0<Q)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D) :
    (∀ ⦃x y⦄, G.fullGraph.Adj x y →
      |stripTime u v U Q a b x-stripTime u v U Q a b y|≤D/U+D/Q) ∧
    (∀ ⦃x y⦄, G.fullGraph.Adj x y →
      |stripHeight u v U Q a b x-stripHeight u v U Q a b y|≤D/U+D/Q) := by
  have hsum : ∀ ⦃x y⦄, G.fullGraph.Adj x y →
      |Corridor.sign a*(u x-u y)/U|+|Corridor.sign b*(v x-v y)/Q|≤D/U+D/Q := by
    intro x y hxy
    rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ]
    exact add_le_add (div_le_div_of_nonneg_right (hu hxy) hU.le)
      (div_le_div_of_nonneg_right (hv hxy) hQ.le)
  constructor
  · intro x y hxy
    calc
      _ = |Corridor.sign a*(u x-u y)/U+Corridor.sign b*(v x-v y)/Q| := by
        congr 1; unfold stripTime; ring
      _ ≤ _ := (abs_add_le _ _).trans (hsum hxy)
  · intro x y hxy
    calc
      _ = |Corridor.sign a*(u x-u y)/U-Corridor.sign b*(v x-v y)/Q| := by
        congr 1; unfold stripHeight; ring
      _ ≤ _ := (abs_sub _ _).trans (hsum hxy)

lemma longitudinal_exit_boxMove (u v : V → ℝ) (o : V) (m : ℕ)
    (U Q W D eps : ℝ) (a b : Bool) (huo : u o=0) (hvo : v o=0)
    (hU : 0<U) (hQ : 0<Q) (heps : 0<eps) (hep : eps<1/10)
    (hDU : D/U≤eps/1000) (hWQ : W/Q≤eps/1000) :
    G.axisExit u v (G.vertexBall o m) U W D a ⊆
      G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o 1 := by
  intro ω hω
  obtain ⟨x,hx,y,w,hw,hy,hy'⟩ := (G.axisExit_iff u v (G.vertexBall o m) U W D a ω).mp hω
  have ho : stripTime u v U Q a b o=0 ∧ stripHeight u v U Q a b o=0 := by
    simp [stripTime,stripHeight,huo,hvo]
  have hpath : ∀ x∈w.support,
      |stripTime u v U Q a b x|≤30 ∧ |stripHeight u v U Q a b x|≤30 := by
    intro z hz
    have hb := strip_coordinate_bounds u v U Q a b hU hQ z
    have h1 := div_le_div_of_nonneg_right (hw z hz).1 hU.le
    have h2 := div_le_div_of_nonneg_right (hw z hz).2 hQ.le
    have huq : (U+D)/U=1+D/U := by rw [add_div,div_self hU.ne']
    rw [huq] at h1
    constructor <;> linarith [hb.1,hb.2]
  have he1 := signed_exit_error a (u y) U D hU hy hy'
  have he2 : |Corridor.sign b*v y/Q|≤W/Q := by
    rw [signed_div_abs b _ _ hQ]
    exact div_le_div_of_nonneg_right (hw y w.end_mem_support).2 hQ.le
  refine ⟨x,hx,y,w,?_,?_,?_⟩
  · simpa only [ho.1,ho.2,sub_zero] using hpath
  · rw [ho.1,zero_add]
    have h := abs_add_le (Corridor.sign a*u y/U-1) (Corridor.sign b*v y/Q)
    have heq : stripTime u v U Q a b y-1=(Corridor.sign a*u y/U-1)+Corridor.sign b*v y/Q := by
      unfold stripTime; ring
    rw [heq]
    linarith
  · rw [ho.2,zero_add]
    have h := abs_sub (Corridor.sign a*u y/U-1) (Corridor.sign b*v y/Q)
    have heq : stripHeight u v U Q a b y-1=(Corridor.sign a*u y/U-1)-Corridor.sign b*v y/Q := by
      unfold stripHeight; ring
    rw [heq]
    linarith

lemma transverse_exit_boxMove (u v : V → ℝ) (o : V) (m : ℕ)
    (U Q M D eps : ℝ) (a b : Bool) (huo : u o=0) (hvo : v o=0)
    (hU : 0<U) (hQ : 0<Q) (heps : 0<eps) (hep : eps<1/10)
    (hMU : M/U≤eps/1000) (hDQ : D/Q≤eps/1000) :
    G.axisExit v u (G.vertexBall o m) Q M D b ⊆
      G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o (-1) := by
  intro ω hω
  obtain ⟨x,hx,y,w,hw,hy,hy'⟩ := (G.axisExit_iff v u (G.vertexBall o m) Q M D b ω).mp hω
  have ho : stripTime u v U Q a b o=0 ∧ stripHeight u v U Q a b o=0 := by
    simp [stripTime,stripHeight,huo,hvo]
  have hpath : ∀ x∈w.support,
      |stripTime u v U Q a b x|≤30 ∧ |stripHeight u v U Q a b x|≤30 := by
    intro z hz
    have hb := strip_coordinate_bounds u v U Q a b hU hQ z
    have h1 := div_le_div_of_nonneg_right (hw z hz).1 hQ.le
    have h2 := div_le_div_of_nonneg_right (hw z hz).2 hU.le
    have huq : (Q+D)/Q=1+D/Q := by rw [add_div,div_self hQ.ne']
    rw [huq] at h1
    constructor <;> linarith [hb.1,hb.2]
  have he1 := signed_exit_error b (v y) Q D hQ hy hy'
  have he2 : |Corridor.sign a*u y/U|≤M/U := by
    rw [signed_div_abs a _ _ hU]
    exact div_le_div_of_nonneg_right (hw y w.end_mem_support).2 hU.le
  refine ⟨x,hx,y,w,?_,?_,?_⟩
  · simpa only [ho.1,ho.2,sub_zero] using hpath
  · rw [ho.1,zero_add]
    have h := abs_add_le (Corridor.sign a*u y/U) (Corridor.sign b*v y/Q-1)
    have heq : stripTime u v U Q a b y-1=Corridor.sign a*u y/U+(Corridor.sign b*v y/Q-1) := by
      unfold stripTime; ring
    rw [heq]
    linarith
  · rw [ho.2,zero_add]
    have h := abs_sub (Corridor.sign a*u y/U) (Corridor.sign b*v y/Q-1)
    have heq : stripHeight u v U Q a b y-(-1)=Corridor.sign a*u y/U-(Corridor.sign b*v y/Q-1) := by
      unfold stripHeight; ring
    rw [heq]
    linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
