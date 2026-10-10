import OAI.Geometry.Convex.GeneralMahler.Hermite.H
import OAI.Geometry.Convex.GeneralMahler.HMatrix

namespace OAI
/-! Tensor Hermite modes, Gaussian multivariate. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Real ProbabilityTheory
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace GeneralMahler.HMode
open Layers
variable {m:ℕ}
abbrev MI (m:ℕ) := Fin m→ℕ
abbrev e (i:Fin m) : Rn m := EuclideanSpace.basisFun (Fin m) ℝ i
def MM (a:MI m) (x:Rn m) := ∏ i,H (a i) (x i)
def inc (a:MI m) (i:Fin m) := Function.update a i (a i+1)
def decM (a:MI m) (i:Fin m) := Function.update a i (a i-1)
lemma inc_at (a:MI m) (i) : inc a i i=a i+1 := Function.update_self ..
lemma dec_at (a:MI m) (i) : decM a i i=a i-1 := Function.update_self ..

lemma p_finprod {I X:Type*} [SeminormedAddCommGroup X] {f:I→X→ℝ} (h:∀ i,PolyBound (f i)) (s:Finset I) :
    PolyBound fun x=> ∏ i ∈ s,f i x := by
  classical
  induction s using Finset.induction with
  | empty=>simpa using PolyBound.const (X:=X) (1:ℝ)
  | insert i s hi ih=>simpa [hi] using (h i).mul ih
lemma M_poly (a:MI m) : PolyBound (MM a) :=
  p_finprod (f:=fun i (x:Rn m)=> H (a i) (x i)) (fun i=>((ht _).poly).comp (PolyBound.clm (ProjField.coord i))) _
lemma M_diff (a:MI m) : Differentiable ℝ (MM a) := by
  classical
  have h (u:Finset (Fin m)) : Differentiable ℝ (fun x:Rn m=> ∏ i∈u,H (a i) (x i)) := by
    induction u using Finset.induction with
    | empty=> simp
    | insert i u hi ih=>
      have he : Differentiable ℝ (fun x:Rn m=>H (a i) (x i)) :=
        (ht (a i)).diff.comp (ProjField.coord i).differentiable
      simpa only [Finset.prod_insert hi] using he.fun_mul ih
  exact h _
lemma M_cont (a:MI m) : Continuous (MM a) := (M_diff a).continuous

lemma M_inner (a b:MI m) :
    (∫ x,MM a x*MM b x ∂normal m) = if a=b then 1 else 0 := by
  classical
  let f := fun i:Fin m=>fun x:ℝ=> H (a i) x*H (b i) x
  let T := MeasurableEquiv.toLp 2 (Fin m→ℝ)
  have he : normal m=(Measure.pi fun _ : Fin m=>GeneralMahler.gamma).map T :=
    ProbabilityTheory.map_pi_eq_stdGaussian.symm
  have hf (i:Fin m) := avg_o (a i) (b i)
  rw [he,integral_map_equiv]
  have hx (x:Fin m→ℝ) : MM a (T x)*MM b (T x) = ∏ i, f i (x i) := by
    unfold MM f T; rw [Finset.prod_mul_distrib]; rfl
  simp_rw [hx]; rw [integral_fintype_prod_eq_prod]; simp_rw [gamma_area]
  simp_rw [show ∀ i,ga (f i)=_ from hf]
  by_cases h:a=b
  · subst b; simp
  rw [ite_eq_right h]; push Not at h
  have h' : ∃ i,a i≠b i := by by_contra! hh; exact h (funext hh)
  obtain ⟨i,hi⟩ := h'
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma factor (a:MI m) (x:Rn m) (i:Fin m) :
    MM a x=H (a i) (x i)*∏ j∈Finset.univ.erase i,H (a j) (x j) :=
  (Finset.mul_prod_erase (s:=Finset.univ) _ (Finset.mem_univ i)).symm

lemma factor_upd (a:MI m) (x:Rn m) (i:Fin m) (n:ℕ) :
    MM (Function.update a i n) x=
      H n (x i)*∏ j∈Finset.univ.erase i,H (a j) (x j) := by
  rw [factor _ _ i,Function.update_self]
  congr 1
  apply Finset.prod_congr rfl; intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma ee (x:Rn m) (i) : ⟪x,e i⟫=x i := by
  rw [real_inner_comm]; exact ((EuclideanSpace.basisFun ..).repr_apply_apply _ _).symm
lemma ladder (a:MI m) (i) (x:Rn m) :
    x i*MM a x=sn (a i+1)*MM (inc a i) x + sn (a i)*MM (decM a i) x := by
  unfold inc decM
  rw [factor_upd,factor_upd,factor a x i,← mul_assoc,← mul_assoc,← mul_assoc,raise,Hder]
  ring
lemma dir_line (x:Rn m) (i:Fin m) :
    HasDerivAt (fun t:ℝ=>x+t • e i) (e i) 0 := by
  convert (((hasDerivAt_id' (0:ℝ)).smul_const (e i)).const_add x) using 1
  all_goals first | rfl | simp
lemma part_lower (a:MI m) (i) (x:Rn m) :
    fderiv ℝ (MM a) x (e i)=sn (a i)*MM (decM a i) x := by
  let L := fun t:ℝ=> x+t • e i
  have hL : L 0=x := by simp [L]
  let v := ∏ j ∈ Finset.univ.erase i,H (a j) (x j)
  have he : MM a ∘ L=fun t=> H (a i) (x i+t)*v := by
    ext t
    rw [Function.comp_apply,factor _ _ i,show L t i=x i+t from ?_]
    · congr 1
      apply Finset.prod_congr rfl; intro j hj
      have hh : i≠j := (Finset.ne_of_mem_erase hj).symm
      simp [L,e,hh]
    simp [L,e]
  have hi : HasDerivAt (MM a ∘ L) (fderiv ℝ (MM a) x (e i)) 0 := by
    convert ((M_diff a (L 0)).hasFDerivAt.comp_hasDerivAt 0 (dir_line x i)) using 1
    all_goals first | rfl | rw [hL]
  have hu : HasDerivAt (MM a ∘ L) (deriv (H (a i)) (x i)*v) 0 := by
    rw [he]
    have hh := ((((ht (a i)).diff (x i+ (0:ℝ))).hasDerivAt).comp 0
      ((hasDerivAt_id' (0:ℝ)).const_add (x i))).mul_const v
    simpa [Function.comp_def] using hh
  rw [hi.unique hu,Hder, decM,factor_upd]
  unfold v; ring
end GeneralMahler.HMode

end

end OAI
