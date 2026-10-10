import Mathlib
import OAI.Probability.LatticeSurface.Convexity.ElementaryKernels

namespace OAI

noncomputable section

namespace ClusterDisplacement

open Set

variable {V : Type*} [Fintype V]

lemma subtype_sum_le (W : Set V) [DecidablePred (·∈W)] (f : V → ℝ) (hf : ∀x,0≤f x) :
    (∑x : W,f x)≤∑x,f x := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype (fun x => x∈W) f
  have hn : 0≤∑x : {x // x∉W},f x := Finset.sum_nonneg fun x _ => hf x
  linarith

noncomputable def zeroExtend (W : Set V) [DecidablePred (·∈W)] (u : W → ℝ) (x : V) : ℝ :=
  if hx : x∈W then u ⟨x,hx⟩ else 0

omit [Fintype V] in
lemma zeroExtend_coe (W : Set V) [DecidablePred (·∈W)] (u : W → ℝ) (x : W) : zeroExtend W u x=u x := by simp [zeroExtend,x.property]

lemma sum_zeroExtend (W : Set V) [DecidablePred (·∈W)] (u : W → ℝ) : (∑x,zeroExtend W u x)=∑x,u x := by
  classical
  exact Finset.sum_congr_set W (zeroExtend W u) u (fun x hx => by simp [zeroExtend,hx]) (fun x hx => by simp [zeroExtend,hx])

def Kernel.restrict (K : Kernel V) (W : Set V) [DecidablePred (·∈W)] : Kernel W where
  val x y := K.val x y
  nonneg x y := K.nonneg x y
  row x := (subtype_sum_le W (K.val x) (K.nonneg x)).trans (K.row x)
  col y := (subtype_sum_le W (fun x => K.val x y) (fun x => K.nonneg x y)).trans (K.col y)

lemma Kernel.restrict_apply (K : Kernel V) (W : Set V) [DecidablePred (·∈W)] (u : W → ℝ) (x : W) :
    (K.restrict W).apply u x=K.apply (zeroExtend W u) x := by
  classical
  symm
  apply Finset.sum_congr_set W
  · intro y hy
    simp only [zeroExtend,dite_eq_left hy,Kernel.restrict]
  · intro y hy
    simp only [zeroExtend,dite_eq_right hy,mul_zero]

lemma Kernel.restrict_firm (K : Kernel V) (hK : Firm K) (W : Set V) [DecidablePred (·∈W)] : Firm (K.restrict W) := by
  classical
  rw [firm_iff]
  intro u
  have he : (∑x,zeroExtend W u x*K.apply (zeroExtend W u) x)=∑x : W,u x*(K.restrict W).apply u x := by
    apply Finset.sum_congr_set W
    · intro x hx
      rw [show zeroExtend W u x=u ⟨x,hx⟩ by simp [zeroExtend,hx]]
      rw [Kernel.restrict_apply]
    · intro x hx
      simp only [zeroExtend,dite_eq_right hx,zero_mul]
  calc
    energy ((K.restrict W).apply u)=∑x : W,(K.apply (zeroExtend W u) x)^2 := by simp only [energy,Kernel.restrict_apply]
    _ ≤ energy (K.apply (zeroExtend W u)) := subtype_sum_le W _ (fun x => sq_nonneg _)
    _ ≤ ∑x,zeroExtend W u x*K.apply (zeroExtend W u) x := (firm_iff K).mp hK _
    _ = _ := he

omit [Fintype V] in
lemma zeroExtend_restrict (W : Set V) [DecidablePred (·∈W)] (u : V → ℝ) (hu : ∀x∉W,u x=0) :
    zeroExtend W (fun x : W => u x)=u := by
  funext x
  by_cases hx : x∈W
  · simp [zeroExtend,hx]
  · simp [zeroExtend,hx,hu x hx]

lemma Kernel.restrict_apply_of_zero (K : Kernel V) (W : Set V) [DecidablePred (·∈W)] (u : V → ℝ) (hu : ∀x∉W,u x=0) (x : W) :
    (K.restrict W).apply (fun y => u y) x=K.apply u x := by
  rw [Kernel.restrict_apply,zeroExtend_restrict W u hu]

end ClusterDisplacement

end

end OAI
