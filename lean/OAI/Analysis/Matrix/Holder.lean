import Mathlib
import OAI.Analysis.Matrix.TensorMoment

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
/- Required analytic interpolation for the matrix trace Hölder step06 (23).
A bounded holomorphic function on a tube over a box is bounded on the tube
over the convex hull of its bounded vertices. No Schatten assertion assumed. -/
noncomputable section
open Set Complex
open scoped BigOperators Topology
namespace CoordinateSweeps.TraceHolder

variable {ι : Type*} [Fintype ι]

def inBox (M : ℝ) (x : ι → ℝ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ M

def tubeUnit (f : (ι → ℂ) → ℂ) (x : ι → ℝ) : Prop :=
  ∀ z : ι → ℂ, (∀ i, (z i).re=x i) → ‖f z‖ ≤ 1

lemma tubeUnitConvex {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    {M B : ℝ} (hB : ∀ z : ι → ℂ, inBox M (fun i => (z i).re) → ‖f z‖ ≤ B) :
    Convex ℝ {x : ι → ℝ | inBox M x ∧ tubeUnit f x} := by
  intro x hx y hy a b ha hb hab
  have habox : inBox M (a • x+b • y) := by
    intro i
    change 0 ≤ a*x i+b*y i ∧ a*x i+b*y i ≤ M
    constructor
    · exact add_nonneg (mul_nonneg ha (hx.1 i).1) (mul_nonneg hb (hy.1 i).1)
    · calc
        _ ≤ a*M+b*M := add_le_add
          (mul_le_mul_of_nonneg_left (hx.1 i).2 ha)
          (mul_le_mul_of_nonneg_left (hy.1 i).2 hb)
        _ = M := by rw [← add_mul,hab,one_mul]
  refine ⟨habox,?_⟩
  intro z hz
  let δ : ι → ℂ := fun i => ((y i-x i : ℝ) : ℂ)
  let g : ℂ → ℂ := fun w => f (z+(w-(b : ℂ)) • δ)
  have hgd : Differentiable ℂ g := by
    exact hf.comp (((differentiable_id.sub_const (b : ℂ)).smul_const δ).const_add z)
  have hre (w : ℂ) (i : ι) :
      (z i+(w-(b : ℂ))*δ i).re=(1-w.re)*x i+w.re*y i := by
    simp only [δ,add_re,mul_re,sub_re,ofReal_re,ofReal_im,mul_zero,sub_zero,hz]
    change a*x i+b*y i+(w.re-b)*(y i-x i)=_
    rw [show a=1-b by linarith]
    ring
  have hgB (w : ℂ) (hw : w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) : ‖g w‖ ≤ B := by
    apply hB
    intro i
    change 0 ≤ (z i+(w-(b : ℂ))*δ i).re ∧
      (z i+(w-(b : ℂ))*δ i).re ≤ M
    rw [hre]
    have hw0 : 0 ≤ w.re := hw.1
    have hw1 : w.re ≤ 1 := hw.2
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) (hx.1 i).1)
        (mul_nonneg hw0 (hy.1 i).1)
    · calc
        _ ≤ (1-w.re)*M+w.re*M := add_le_add
          (mul_le_mul_of_nonneg_left (hx.1 i).2 (by linarith))
          (mul_le_mul_of_nonneg_left (hy.1 i).2 hw0)
        _ = M := by ring
  have hl (w : ℂ) (hw : w.re=0) : ‖g w‖ ≤ 1 := by
    apply hx.2
    intro i
    change (z i+(w-(b : ℂ))*δ i).re=x i
    rw [hre,hw]; ring
  have hu (w : ℂ) (hw : w.re=1) : ‖g w‖ ≤ 1 := by
    apply hy.2
    intro i
    change (z i+(w-(b : ℂ))*δ i).re=y i
    rw [hre,hw]; ring
  have hbb : (b : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    exact ⟨hb,by simpa using show b ≤ 1 by linarith⟩
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := g) (z := (b : ℂ)) (a := (1 : ℝ)) (b := (1 : ℝ)) (l := 0) (u := 1)
    (by norm_num) hbb hgd.diffContOnCl (by
      exact ⟨B,fun w hw => by rcases hw with ⟨w,hw,rfl⟩; exact hgB w hw⟩)
    hl hu
  simpa [g] using h

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/- Equal-weight multivariate interpolation. At each vertex a single
coordinate has real part card ι; all imaginary parts remain unrestricted. -/
theorem tube_barycenter {f : (ι → ℂ) → ℂ} (hf : Differentiable ℂ f)
    {B : ℝ} (hB : ∀ z : ι → ℂ,
      inBox (Fintype.card ι) (fun i => (z i).re) → ‖f z‖ ≤ B)
    (hv : ∀ j, tubeUnit f (fun i => if i=j then Fintype.card ι else 0)) :
    tubeUnit f (fun _ => 1) := by
  let N : ℝ := Fintype.card ι
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hc := tubeUnitConvex hf hB
  have hw : ∑ _ : ι, N⁻¹=(1 : ℝ) := by simp [N,hN.ne']
  have hs := hc.sum_mem (t := Finset.univ) (w := fun _ : ι => N⁻¹)
    (z := fun j i => if i=j then (Fintype.card ι : ℝ) else 0)
    (fun _ _ => inv_nonneg.mpr hN.le) hw (by
      intro j hj
      refine ⟨?_,hv j⟩
      intro i
      dsimp only
      split_ifs
      · exact ⟨hN.le,le_rfl⟩
      · exact ⟨le_rfl,hN.le⟩)
  have he : (∑ j : ι, N⁻¹ • (fun i => if i=j then (Fintype.card ι : ℝ) else 0))=
      (fun _ : ι => (1 : ℝ)) := by
    funext i
    simp [Finset.sum_apply,Pi.smul_apply,N,hN.ne']
  rw [he] at hs
  exact hs.2

end CoordinateSweeps.TraceHolder

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma entry_norm_le (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let v : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have hv : ‖v‖=1 := by simp [v]
  have h := A.l2_opNorm_mulVec v
  have hi := PiLp.norm_apply_le ((EuclideanSpace.equiv n ℂ).symm (A.mulVec v)) i
  have he : ((EuclideanSpace.equiv n ℂ).symm (A.mulVec v)) i=A i j := by simp [v]
  rw [he] at hi
  rw [hv,mul_one] at h
  exact hi.trans h

lemma trace_norm_le (A : Matrix n n ℂ) :
    ‖Matrix.trace A‖ ≤ (Fintype.card n : ℝ)*‖A‖ := by
  calc
    _ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : n, ‖A‖ := Finset.sum_le_sum (fun i _ => entry_norm_le A i i)
    _ = _ := by simp

lemma trace_diagonal_bound (d : n → ℂ) (B : Matrix n n ℂ) (hB : ‖B‖ ≤ 1) :
    ‖Matrix.trace (Matrix.diagonal d*B)‖ ≤ ∑ i, ‖d i‖ := by
  simp only [Matrix.trace,Matrix.diag,Matrix.diagonal_mul]
  calc
    _ ≤ ∑ i, ‖d i*B i i‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) ((entry_norm_le B i i).trans hB))

lemma list_prod_norm_le_one [Nonempty n] (L : List (Matrix n n ℂ)) (hL : ∀ A ∈ L, ‖A‖ ≤ 1) :
    ‖L.prod‖ ≤ 1 := by
  induction L with
  | nil => simp
  | cons A L ih =>
    rw [List.prod_cons]
    have hA := hL A (by simp)
    have htail := ih (fun B hB => hL B (by simp [hB]))
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hA).trans htail)

lemma differentiable_matrix_list_prod_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : List (E → Matrix n n ℂ))
    (hL : ∀ f ∈ L, ∀ i j, Differentiable ℂ (fun z => f z i j)) :
    ∀ i j, Differentiable ℂ (fun z => (L.map (fun f => f z)).prod i j) := by
  induction L with
  | nil => intro i j; exact differentiable_const ((1 : Matrix n n ℂ) i j)
  | cons f L ih =>
    intro i j
    simp only [List.map_cons,List.prod_cons,Matrix.mul_apply]
    apply Differentiable.fun_sum
    intro k hk
    exact (hL f (by simp) i k).mul (ih (fun g hg => hL g (by simp [hg])) k j)

def positivePower (x : ℝ) (z : ℂ) : ℂ :=
  if x=0 then 0 else Complex.exp ((Real.log x : ℂ)*z)

lemma positivePower_differentiable (x : ℝ) : Differentiable ℂ (positivePower x) := by
  unfold positivePower
  split_ifs
  · exact differentiable_const 0
  · fun_prop

lemma positivePower_one {x : ℝ} (hx : 0 ≤ x) : positivePower x 1=(x : ℂ) := by
  by_cases h : x=0
  · simp [positivePower,h]
  · simp [positivePower,h,← Complex.ofReal_exp,Real.exp_log (hx.lt_of_ne' h)]

lemma positivePower_norm_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    {z : ℂ} (hz : 0 ≤ z.re) : ‖positivePower x z‖ ≤ 1 := by
  by_cases h : x=0
  · simp [positivePower,h]
  · rw [positivePower,ite_eq_right h,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hx hx1) hz)

lemma positivePower_norm_nat {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 0 < m)
    {z : ℂ} (hz : z.re=m) : ‖positivePower x z‖=x^m := by
  by_cases h : x=0
  · simp [positivePower,h,hm.ne']
  · rw [positivePower,ite_eq_right h,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hz]
    rw [mul_comm,Real.exp_nat_mul,Real.exp_log (hx.lt_of_ne' h)]

lemma norm_mul_diag_mul_le_one (U V : Matrix n n ℂ) (d : n → ℂ)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) (hd : ∀ i, ‖d i‖ ≤ 1) :
    ‖U*Matrix.diagonal d*V‖ ≤ 1 := by
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hV
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) hU).trans
  rw [Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr hd

/- Ordered analytic product; factors may be noncommuting. -/
def traceFamily {m : ℕ} (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (z : Fin m → ℂ) : ℂ :=
  Matrix.trace ((List.ofFn (fun j => U j*Matrix.diagonal (fun i => positivePower (dval j i) (z j))*V j)).prod)

lemma differentiable_framed_diag_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U V : Matrix n n ℂ) (f : n → E → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (a b : n) :
    Differentiable ℂ (fun z => (U*Matrix.diagonal (fun i => f i z)*V) a b) := by
  have he (z : E) : (U*Matrix.diagonal (fun i => f i z)*V) a b=
      ∑ k, (U a k*f k z)*V k b := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  simp_rw [he]
  apply Differentiable.fun_sum
  intro k hk
  exact ((hf k).const_mul (U a k)).mul_const (V k b)

lemma traceFamily_differentiable {m : ℕ} (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ) :
    Differentiable ℂ (traceFamily U V dval) := by
  let F : Fin m → (Fin m → ℂ) → Matrix n n ℂ := fun j z =>
    U j*Matrix.diagonal (fun i => positivePower (dval j i) (z j))*V j
  have hF (j : Fin m) (a b : n) : Differentiable ℂ (fun z => F j z a b) := by
    apply differentiable_framed_diag_entries
    intro i
    exact (positivePower_differentiable (dval j i)).comp (differentiable_apply j)
  have hp := differentiable_matrix_list_prod_entries (List.ofFn F) (by
    intro f hf
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hf
    exact hF j)
  have ht : Differentiable ℂ (fun z => ∑ i, ((List.ofFn F).map (fun f => f z)).prod i i) := by
    apply Differentiable.fun_sum
    intro i hi
    exact hp i i
  have he : (fun z => ∑ i, ((List.ofFn F).map (fun f => f z)).prod i i)=
      traceFamily U V dval := by
    funext z
    simp only [traceFamily,F,List.map_ofFn,Matrix.trace,Matrix.diag,Function.comp_def]
  rw [he] at ht
  exact ht

lemma traceFamily_bound [Nonempty n] {m : ℕ} (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) (hdval : ∀ j i, 0 ≤ dval j i ∧ dval j i ≤ 1)
    (z : Fin m → ℂ) (hz : ∀ j, 0 ≤ (z j).re) :
    ‖traceFamily U V dval z‖ ≤ Fintype.card n := by
  apply (trace_norm_le _).trans
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  apply list_prod_norm_le_one
  intro A hA
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hA
  exact norm_mul_diag_mul_le_one (U j) (V j) _ (hU j) (hV j)
    (fun i => positivePower_norm_le (hdval j i).1 (hdval j i).2 (hz j))

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma single_diagonal_trace_bound {m : ℕ} (F : Fin m → Matrix n n ℂ) (j : Fin m)
    (U V : Matrix n n ℂ) (d : n → ℂ) (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hFj : F j=U*Matrix.diagonal d*V) (hF : ∀ k, k≠j → ‖F k‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn F).prod‖ ≤ ∑ i, ‖d i‖ := by
  let L := List.ofFn F
  have hj : j.val < L.length := by simp [L]
  have hnorm : ∀ l ∈ L.take j.val, ‖l‖ ≤ 1 := by
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_take_iff_getElem.mp hl
    have hkm : k < m := by simpa [L] using (lt_min_iff.mp hk).2
    change ‖(List.ofFn F)[k]‖ ≤ 1
    rw [List.getElem_ofFn]
    apply hF
    intro hh
    have he := congrArg Fin.val hh
    exact (Nat.ne_of_lt (lt_min_iff.mp hk).1) he
  have tnorm : ∀ l ∈ L.drop (j.val+1), ‖l‖ ≤ 1 := by
    intro l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_drop_iff_getElem.mp hl
    have hkm : j.val+1+k < m := by simpa [L,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hk
    change ‖(List.ofFn F)[j.val+1+k]'(by simpa using hkm)‖ ≤ 1
    rw [List.getElem_ofFn]
    apply hF
    intro hh
    have he := congrArg Fin.val hh
    dsimp only at he
    omega
  have hhead := list_prod_norm_le_one (L.take j.val) hnorm
  have htail := list_prod_norm_le_one (L.drop (j.val+1)) tnorm
  have he : L.prod=(L.take j.val).prod*(U*Matrix.diagonal d*V)*(L.drop (j.val+1)).prod := by
    rw [← List.prod_take_mul_prod_drop L j.val,List.drop_eq_getElem_cons hj,List.prod_cons]
    have hg : L[j.val]=F j := by simp [L]
    rw [hg,hFj]
    simp only [mul_assoc]
  change ‖Matrix.trace L.prod‖ ≤ _
  rw [he]
  have hcycle : Matrix.trace ((L.take j.val).prod*(U*Matrix.diagonal d*V)*
      (L.drop (j.val+1)).prod)=Matrix.trace (Matrix.diagonal d*
        (V*(L.drop (j.val+1)).prod*(L.take j.val).prod*U)) := by
    calc
      _ = Matrix.trace (((L.take j.val).prod*U)*
        (Matrix.diagonal d*(V*(L.drop (j.val+1)).prod))) := by simp only [mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_comm]; simp only [mul_assoc]
  rw [hcycle]
  apply trace_diagonal_bound
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hU
  apply (norm_mul_le _ _).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans hhead
  exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hV).trans htail)

lemma traceFamily_vertex {m : ℕ} (hm : 0 < m)
    (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) (hdval : ∀ j i, 0 ≤ dval j i ∧ dval j i ≤ 1)
    (hs : ∀ j, ∑ i, (dval j i)^m ≤ 1) (j : Fin m) :
    tubeUnit (traceFamily U V dval) (fun k => if k=j then m else 0) := by
  intro z hz
  have hzj : (z j).re=m := by simpa using hz j
  have hzk (k : Fin m) (hk : k≠j) : (z k).re=0 := by simpa [hk] using hz k
  apply (single_diagonal_trace_bound
    (fun k => U k*Matrix.diagonal (fun i => positivePower (dval k i) (z k))*V k) j
    (U j) (V j) (fun i => positivePower (dval j i) (z j)) (hU j) (hV j) rfl ?_).trans
  · simpa only [positivePower_norm_nat (hdval j _).1 hm hzj] using hs j
  · intro k hk
    exact norm_mul_diag_mul_le_one (U k) (V k) _ (hU k) (hV k)
      (fun i => positivePower_norm_le (hdval k i).1 (hdval k i).2 (by rw [hzk k hk]))

/- The complete normalized diagonal-factor trace Hölder estimate, for
arbitrarily many NONCOMMUTING factors. It is the analytic heart of06 eq23. -/
theorem diagonal_trace_holder {m : ℕ} (hm : 0 < m)
    (U V : Fin m → Matrix n n ℂ) (dval : Fin m → n → ℝ)
    (hU : ∀ j, ‖U j‖ ≤ 1) (hV : ∀ j, ‖V j‖ ≤ 1) (hdval : ∀ j i, 0 ≤ dval j i ∧ dval j i ≤ 1)
    (hs : ∀ j, ∑ i, (dval j i)^m ≤ 1) :
    ‖Matrix.trace ((List.ofFn (fun j => U j*Matrix.diagonal
      (fun i => ((dval j i : ℝ) : ℂ))*V j)).prod)‖ ≤ 1 := by
  let : NeZero m := ⟨hm.ne'⟩
  have h := tube_barycenter (traceFamily_differentiable U V dval)
    (B := (Fintype.card n : ℝ))
    (fun z hz => traceFamily_bound U V dval hU hV hdval z (fun j => (hz j).1))
    (fun j => by simpa using traceFamily_vertex hm U V dval hU hV hdval hs j)
  have hh := h (fun _ => 1) (by simp)
  simpa [traceFamily,positivePower_one (hdval _ _).1] using hh

end CoordinateSweeps.TraceHolder

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev gramHermitian (A : Matrix n n ℂ) := Matrix.isHermitian_conjTranspose_mul_self A

def singular (A : Matrix n n ℂ) (i : n) : ℝ := Real.sqrt ((gramHermitian A).eigenvalues i)

def rightBasis (A : Matrix n n ℂ) : Matrix.unitaryGroup n ℂ :=
  (gramHermitian A).eigenvectorUnitary

def rawPolar (A : Matrix n n ℂ) : Matrix n n ℂ :=
  A*(rightBasis A : Matrix n n ℂ)

def leftFrame (A : Matrix n n ℂ) : Matrix n n ℂ :=
  rawPolar A*Matrix.diagonal (fun i => (((singular A i)⁻¹ : ℝ) : ℂ))

lemma singular_nonneg (A : Matrix n n ℂ) (i : n) : 0 ≤ singular A i := Real.sqrt_nonneg _

lemma singular_sq (A : Matrix n n ℂ) (i : n) :
    singular A i^2=(gramHermitian A).eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

lemma rawPolar_gram (A : Matrix n n ℂ) :
    (rawPolar A).conjTranspose*rawPolar A=Matrix.diagonal
      (fun i => ((gramHermitian A).eigenvalues i : ℂ)) := by
  have h := (gramHermitian A).conjStarAlgAut_star_eigenvectorUnitary
  simpa only [rawPolar,rightBasis,Matrix.conjTranspose_mul,Unitary.conjStarAlgAut_star_apply,
    Matrix.star_eq_conjTranspose,mul_assoc,Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal] using h

omit [DecidableEq n] in
lemma zero_gram_column {B : Matrix n n ℂ} (j : n) (h : (B.conjTranspose*B) j j=0) :
    ∀ i, B i j=0 := by
  have hh := congrArg Complex.re h
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Complex.re_sum,Complex.star_def,
    Complex.conj_mul',Complex.zero_re] at hh
  have hsum : ∑ i, ‖B i j‖^2=0 := by
    simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖B i j‖)).mp hsum
  intro i
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hzero i (Finset.mem_univ i)))

lemma rawPolar_zero_column (A : Matrix n n ℂ) (j : n) (hj : singular A j=0) :
    ∀ i, rawPolar A i j=0 := by
  apply zero_gram_column
  rw [rawPolar_gram,Matrix.diagonal_apply_eq,← singular_sq,hj]
  simp

lemma leftFrame_gram (A : Matrix n n ℂ) :
    (leftFrame A).conjTranspose*leftFrame A=
      Matrix.diagonal (fun i => if singular A i=0 then (0 : ℂ) else 1) := by
  simp only [leftFrame,Matrix.conjTranspose_mul,Matrix.diagonal_conjTranspose]
  rw [mul_assoc,← mul_assoc (rawPolar A).conjTranspose,rawPolar_gram,
    Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  rw [← singular_sq]
  by_cases hi : singular A i=0
  · simp [hi]
  · simp [hi,Complex.ofReal_inv,Complex.ofReal_pow]
    field_simp

lemma leftFrame_norm_le (A : Matrix n n ℂ) : ‖leftFrame A‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (leftFrame A)
  rw [leftFrame_gram,Matrix.l2_opNorm_diagonal] at hh
  have hb : ‖fun i => if singular A i=0 then (0 : ℂ) else 1‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    split_ifs <;> simp
  nlinarith [norm_nonneg (leftFrame A)]

lemma rightBasis_star_norm_le [Nonempty n] (A : Matrix n n ℂ) :
    ‖(rightBasis A : Matrix n n ℂ).conjTranspose‖ ≤ 1 := by
  rw [Matrix.l2_opNorm_conjTranspose]
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (rightBasis A : Matrix n n ℂ)
  have hu := Unitary.coe_star_mul_self (rightBasis A)
  rw [Matrix.star_eq_conjTranspose] at hu
  rw [hu,norm_one] at hh
  nlinarith [norm_nonneg (rightBasis A : Matrix n n ℂ)]

lemma polar_factors (A : Matrix n n ℂ) :
    leftFrame A*Matrix.diagonal (fun i => (singular A i : ℂ))*
      (rightBasis A : Matrix n n ℂ).conjTranspose=A := by
  have hh : leftFrame A*Matrix.diagonal (fun i => (singular A i : ℂ))=rawPolar A := by
    ext i j
    simp only [leftFrame,Matrix.mul_diagonal]
    by_cases hj : singular A j=0
    · simp [hj,rawPolar_zero_column A j hj i]
    · rw [mul_assoc]
      simp [hj]
  rw [hh,rawPolar,mul_assoc]
  have hu := Unitary.coe_mul_star_self (rightBasis A)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose] at hu
  rw [hu,mul_one]

lemma trace_moment_singular (A : Matrix n n ℂ) (q : ℕ) :
    (Matrix.trace ((A.conjTranspose*A)^q)).re=∑ i, singular A i^(2*q) := by
  have h := (gramHermitian A).spectral_theorem
  rw [h,← map_pow,Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self,one_mul,Matrix.diagonal_pow,Matrix.trace_diagonal]
  simp only [Complex.re_sum,Function.comp_def,Pi.pow_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_mul,singular_sq]
  simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]

def singularMass (m : ℕ) (A : Matrix n n ℂ) : ℝ := ∑ i, singular A i^m

def schatten (m : ℕ) (A : Matrix n n ℂ) : ℝ := (singularMass m A)^((m : ℝ)⁻¹)

lemma singularMass_nonneg (m : ℕ) (A : Matrix n n ℂ) : 0 ≤ singularMass m A :=
  Finset.sum_nonneg (fun i _ => pow_nonneg (singular_nonneg A i) _)

lemma singularMass_eq_zero (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ)
    (h : singularMass m A=0) : A=0 := by
  have hs (i : n) : singular A i=0 := by
    have hi : singular A i^m ≤ singularMass m A :=
      Finset.single_le_sum (fun i _ => pow_nonneg (singular_nonneg A i) _) (Finset.mem_univ i)
    rw [h] at hi
    have hz : singular A i^m=0 := le_antisymm hi (pow_nonneg (singular_nonneg A i) _)
    exact (pow_eq_zero_iff hm.ne').mp hz
  have hf := polar_factors A
  simp only [hs,Complex.ofReal_zero,Matrix.diagonal_zero,mul_zero,zero_mul] at hf
  exact hf.symm

lemma schatten_nonneg (m : ℕ) (A : Matrix n n ℂ) : 0 ≤ schatten m A :=
  Real.rpow_nonneg (singularMass_nonneg m A) _

lemma schatten_pos (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) :
    0 < schatten m A := by
  apply Real.rpow_pos_of_pos
  exact lt_of_le_of_ne (singularMass_nonneg m A) (Ne.symm (fun hh => hA (singularMass_eq_zero m hm A hh)))

lemma schatten_pow (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) :
    schatten m A ^ m = singularMass m A :=
  Real.rpow_inv_natCast_pow (singularMass_nonneg m A) hm.ne'

lemma normalized_singular_sum (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) :
    ∑ i, (singular A i / schatten m A)^m = 1 := by
  simp_rw [div_pow]
  rw [← Finset.sum_div,schatten_pow m hm A]
  exact div_self (fun hh => hA (singularMass_eq_zero m hm A hh))

lemma normalized_singular_le (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) (i : n) :
    0 ≤ singular A i / schatten m A ∧ singular A i / schatten m A ≤ 1 := by
  have hpos := schatten_pos m hm A hA
  have hi : 0 ≤ singular A i / schatten m A := div_nonneg (singular_nonneg A i) hpos.le
  refine ⟨hi,?_⟩
  have hb : (singular A i / schatten m A)^m ≤ 1 := by
    rw [← normalized_singular_sum m hm A hA]
    exact Finset.single_le_sum (fun j _ => pow_nonneg (div_nonneg (singular_nonneg A j) hpos.le) _) (Finset.mem_univ i)
  by_contra hn
  have hgt : 1 < singular A i / schatten m A := lt_of_not_ge hn
  exact not_lt_of_ge hb (one_lt_pow₀ hgt hm.ne')

lemma normalized_polar (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) (hA : A ≠ 0) :
    (schatten m A : ℂ) • (leftFrame A * Matrix.diagonal
      (fun i => ((singular A i / schatten m A : ℝ) : ℂ)) * (rightBasis A : Matrix n n ℂ).conjTranspose) = A := by
  have hpos := schatten_pos m hm A hA
  have hc : (schatten m A : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [← Matrix.smul_mul,← Matrix.mul_smul]
  have hd : (schatten m A : ℂ) • Matrix.diagonal
      (fun i => ((singular A i / schatten m A : ℝ) : ℂ)) = Matrix.diagonal (fun i => (singular A i : ℂ)) := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Complex.ofReal_div,hc,mul_div_cancel₀]
    · simp [hij]
  rw [hd,polar_factors]

lemma list_prod_scaled {m : ℕ} (c : Fin m → ℂ) (A : Fin m → Matrix n n ℂ) :
    (List.ofFn (fun j => c j • A j)).prod = (∏ j, c j) • (List.ofFn A).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ,List.prod_cons,Fin.prod_univ_succ,List.ofFn_succ,List.prod_cons,ih]
    exact smul_mul_smul_comm _ _ _ _

/- Genuine unnormalized Schatten trace Holder, built from the archived
complete interpolation and polar-frame proofs rather than assumed. -/
theorem matrix_trace_holder [Nonempty n] {m : ℕ} (hm : 0 < m) (A : Fin m → Matrix n n ℂ) :
    ‖Matrix.trace (List.ofFn A).prod‖ ≤ ∏ j, schatten m (A j) := by
  by_cases hA : ∀ j, A j ≠ 0
  · let d := fun j i => singular (A j) i / schatten m (A j)
    let B := fun j => leftFrame (A j) * Matrix.diagonal (fun i => (d j i : ℂ)) *
      (rightBasis (A j) : Matrix n n ℂ).conjTranspose
    have hb : ‖Matrix.trace (List.ofFn B).prod‖ ≤ 1 :=
      diagonal_trace_holder hm (fun j => leftFrame (A j))
        (fun j => (rightBasis (A j) : Matrix n n ℂ).conjTranspose) d
        (fun j => leftFrame_norm_le _) (fun j => rightBasis_star_norm_le _)
        (fun j i => normalized_singular_le m hm (A j) (hA j) i)
        (fun j => (normalized_singular_sum m hm (A j) (hA j)).le)
    have he : A = fun j => (schatten m (A j) : ℂ) • B j := by
      funext j
      exact (normalized_polar m hm (A j) (hA j)).symm
    conv_lhs => rw [he,list_prod_scaled,Matrix.trace_smul,norm_smul]
    have hc : ‖∏ j, (schatten m (A j) : ℂ)‖ = ∏ j, schatten m (A j) := by
      rw [norm_prod]
      apply Finset.prod_congr rfl
      intro j _
      simp [Complex.norm_real,abs_of_nonneg (schatten_nonneg m (A j))]
    rw [hc]
    exact mul_le_of_le_one_right (Finset.prod_nonneg (fun j _ => schatten_nonneg m _)) hb
  · push Not at hA
    obtain ⟨j,hj⟩ := hA
    have hz : (List.ofFn A).prod = 0 := List.prod_eq_zero (List.mem_ofFn.mpr ⟨j,hj⟩)
    rw [hz,Matrix.trace_zero,norm_zero]
    exact Finset.prod_nonneg (fun j _ => schatten_nonneg m _)

lemma schatten_even_eq (q : ℕ) (A : Matrix n n ℂ) :
    schatten (2*q) A = (Matrix.trace ((A.conjTranspose*A)^q)).re ^ ((2*q : ℝ)⁻¹) := by
  rw [trace_moment_singular]
  simp only [schatten,singularMass,Nat.cast_mul,Nat.cast_ofNat]

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n]
open scoped ComplexOrder

lemma trace_mul_pow_comm (A B : Matrix n n ℂ) (q : ℕ) :
    Matrix.trace ((A*B)^q) = Matrix.trace ((B*A)^q) := by
  cases q with
  | zero => rfl
  | succ q =>
    rw [pow_succ,← mul_assoc,mul_pow_mul,Matrix.trace_mul_cycle,← pow_succ']

lemma schatten_adjoint_even (q : ℕ) (A : Matrix n n ℂ) :
    schatten (2*q) A.conjTranspose = schatten (2*q) A := by
  simp only [schatten_even_eq,Matrix.conjTranspose_conjTranspose]
  rw [trace_mul_pow_comm]

lemma trace_moment_norm (q : ℕ) (A : Matrix n n ℂ) :
    ‖Matrix.trace ((A.conjTranspose*A)^q)‖ = singularMass (2*q) A := by
  have ht := ((Matrix.posSemidef_conjTranspose_mul_self A).pow q).trace_nonneg
  rw [← show (Matrix.trace ((A.conjTranspose*A)^q)).re = singularMass (2*q) A from
    trace_moment_singular A q]
  have him : (Matrix.trace ((A.conjTranspose*A)^q)).im=0 := by simpa using ht.2.symm
  have hre : 0 ≤ (Matrix.trace ((A.conjTranspose*A)^q)).re := by simpa using ht.1
  have he : Matrix.trace ((A.conjTranspose*A)^q) =
      ((Matrix.trace ((A.conjTranspose*A)^q)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  conv_lhs => rw [he]
  simp [Complex.norm_real,abs_of_nonneg hre]

lemma schatten_even_pow (q : ℕ) (hq : 0 < q) (A : Matrix n n ℂ) :
    schatten (2*q) A ^ (2*q) = (Matrix.trace ((A.conjTranspose*A)^q)).re := by
  rw [schatten_pow _ (by omega)]
  exact (trace_moment_singular A q).symm

lemma schatten_zero_even (q : ℕ) (hq : 0 < q) :
    schatten (2*q) (0 : Matrix n n ℂ)=0 := by
  apply (pow_eq_zero_iff (show 2*q ≠ 0 by omega)).mp
  rw [schatten_even_pow q hq]
  simp [hq.ne']

lemma matrix_trace_holder_list [Nonempty n] (L : List (Matrix n n ℂ)) (hL : 0 < L.length) :
    ‖Matrix.trace L.prod‖ ≤ (L.map (schatten L.length)).prod := by
  have hh := matrix_trace_holder hL L.get
  rw [← List.prod_ofFn] at hh
  simpa only [List.ofFn_comp', List.ofFn_get] using hh

/- Odd alternating word completing one Gram trace to an even moment. -/
def oddWord (q : ℕ) (A : Matrix n n ℂ) : List (Matrix n n ℂ) :=
  A :: (List.replicate q [A.conjTranspose,A]).flatten

omit [Fintype n] [DecidableEq n] in
lemma oddWord_length (q : ℕ) (A : Matrix n n ℂ) :
    (oddWord q A).length = 2*q+1 := by
  simp [oddWord,List.length_flatten]
  omega

lemma oddWord_prod (q : ℕ) (A : Matrix n n ℂ) :
    (oddWord q A).prod=A*(A.conjTranspose*A)^q := by
  simp [oddWord,List.prod_flatten]

lemma oddWord_schatten_prod (q : ℕ) (A : Matrix n n ℂ) :
    ((oddWord q A).map (schatten (2*(q+1)))).prod =
      schatten (2*(q+1)) A ^ (2*q+1) := by
  simp only [oddWord,List.map_cons,List.map_flatten,List.map_replicate,List.map_nil,
    List.prod_cons,List.prod_nil,List.prod_flatten,List.prod_replicate,
    schatten_adjoint_even,mul_one]
  ring

/- The literal unnormalized even Schatten triangle inequality, for a finite
sum, derived from genuine matrix trace Holder rather than postulated. -/
theorem schatten_even_sum_le [Nonempty n] {I : Type*} [Fintype I] (q : ℕ) (hq : 0 < q)
    (A : I → Matrix n n ℂ) :
    schatten (2*q) (∑ i, A i) ≤ ∑ i, schatten (2*q) (A i) := by
  classical
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  let B := ∑ i, A i
  let t := schatten (2*(r+1)) B
  by_cases hB : B=0
  · change schatten (2*(r+1)) B ≤ _
    rw [hB,schatten_zero_even (r+1) (by omega)]
    exact Finset.sum_nonneg fun i _ => schatten_nonneg _ _
  · have ht : 0 < t := schatten_pos _ (by omega) B hB
    have hc (i : I) :
        ‖Matrix.trace ((A i).conjTranspose * (oddWord r B).prod)‖ ≤
          schatten (2*(r+1)) (A i) * t^(2*r+1) := by
      have hh := matrix_trace_holder_list ((A i).conjTranspose :: oddWord r B) (by simp)
      simpa only [List.length_cons,oddWord_length,show 2*r+1+1=2*(r+1) by omega,
        List.prod_cons,List.map_cons,schatten_adjoint_even,oddWord_schatten_prod] using hh
    have he : Matrix.trace ((B.conjTranspose*B)^(r+1)) =
        ∑ i, Matrix.trace ((A i).conjTranspose*(oddWord r B).prod) := by
      rw [pow_succ',mul_assoc,oddWord_prod]
      change Matrix.trace (((∑ i, A i).conjTranspose)*(B*(B.conjTranspose*B)^r)) = _
      rw [Matrix.conjTranspose_sum,Finset.sum_mul,Matrix.trace_sum]
    have hh : t^(2*(r+1)) ≤ (∑ i, schatten (2*(r+1)) (A i)) * t^(2*r+1) := by
      calc
        _ = ‖Matrix.trace ((B.conjTranspose*B)^(r+1))‖ := by
          change schatten (2*(r+1)) B ^ (2*(r+1)) = _
          rw [trace_moment_norm,schatten_pow _ (by omega)]
        _ ≤ ∑ i, ‖Matrix.trace ((A i).conjTranspose*(oddWord r B).prod)‖ := by
          rw [he]; exact norm_sum_le _ _
        _ ≤ ∑ i, schatten (2*(r+1)) (A i) * t^(2*r+1) := Finset.sum_le_sum (fun i _ => hc i)
        _ = _ := (Finset.sum_mul ..).symm
    have hh' : t * t^(2*r+1) ≤ (∑ i, schatten (2*(r+1)) (A i))*t^(2*r+1) := by
      calc
        _ = t^(2*(r+1)) := by
          rw [show 2*(r+1)=(2*r+1)+1 by omega]
          simp only [pow_succ]
          ring
        _ ≤ _ := hh
    change t ≤ ∑ i, schatten (2*(r+1)) (A i)
    exact (mul_le_mul_iff_left₀ (pow_pos ht (2*r+1))).mp hh'

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma matrix_trace_holder_contractions {m : ℕ} (hm : 0 < m)
    (A C : Fin m → Matrix n n ℂ) (hC : ∀ j, ‖C j‖ ≤ 1) :
    ‖Matrix.trace (List.ofFn (fun j => A j*C j)).prod‖ ≤ ∏ j, schatten m (A j) := by
  by_cases hA : ∀ j, A j ≠ 0
  · let d := fun j i => singular (A j) i / schatten m (A j)
    let V := fun j => (rightBasis (A j) : Matrix n n ℂ).conjTranspose*C j
    let B := fun j => leftFrame (A j) * Matrix.diagonal (fun i => (d j i : ℂ)) * V j
    have hv (j) : ‖V j‖ ≤ 1 := (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (rightBasis_star_norm_le _)).trans (hC j))
    have hb : ‖Matrix.trace (List.ofFn B).prod‖ ≤ 1 :=
      diagonal_trace_holder hm (fun j => leftFrame (A j)) V d
        (fun j => leftFrame_norm_le _) hv
        (fun j i => normalized_singular_le m hm (A j) (hA j) i)
        (fun j => (normalized_singular_sum m hm (A j) (hA j)).le)
    have he : (fun j => A j*C j) = fun j => (schatten m (A j) : ℂ) • B j := by
      funext j
      have hh := congrArg (fun M : Matrix n n ℂ => M*C j) (normalized_polar m hm (A j) (hA j))
      simpa only [B,V,d,Matrix.smul_mul,mul_assoc] using hh.symm
    rw [he,list_prod_scaled,Matrix.trace_smul,norm_smul,norm_prod]
    have hc : (∏ j, ‖(schatten m (A j) : ℂ)‖) = ∏ j, schatten m (A j) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [Complex.norm_real,abs_of_nonneg (schatten_nonneg m (A j))]
    rw [hc]
    exact mul_le_of_le_one_right (Finset.prod_nonneg (fun j _ => schatten_nonneg m _)) hb
  · push Not at hA
    obtain ⟨j,hj⟩ := hA
    have hz : (List.ofFn (fun j => A j*C j)).prod=0 := by
      apply List.prod_eq_zero
      exact List.mem_ofFn.mpr ⟨j,by simp [hj]⟩
    rw [hz,Matrix.trace_zero,norm_zero]
    exact Finset.prod_nonneg (fun j _ => schatten_nonneg m _)

lemma matrix_trace_holder_mixed {m : ℕ} (hm : 0 < m) (A C : Fin m → Matrix n n ℂ) :
    ‖Matrix.trace (List.ofFn (fun j => A j*C j)).prod‖ ≤
      ∏ j, schatten m (A j)*‖C j‖ := by
  by_cases hC : ∀ j, C j ≠ 0
  · let C' := fun j => (‖C j‖⁻¹ : ℂ) • C j
    have hc (j) : ‖C' j‖ ≤ 1 := by
      have hp := norm_pos_iff.mpr (hC j)
      simp [C',norm_smul,Complex.norm_real,hp.ne']
    have hb := matrix_trace_holder_contractions hm A C' hc
    have he : (fun j => A j*C j) = fun j => (‖C j‖ : ℂ) • (A j*C' j) := by
      funext j
      have hp : (‖C j‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hC j)
      have hc' : (‖C j‖ : ℂ) • C' j = C j := by
        ext a b
        simp [C',Matrix.smul_apply,smul_eq_mul,hp]
      rw [← Matrix.mul_smul,hc']
    rw [he,list_prod_scaled,Matrix.trace_smul,norm_smul,norm_prod]
    have hn : (∏ j, ‖(‖C j‖ : ℂ)‖) = ∏ j, ‖C j‖ := by simp
    rw [hn,Finset.prod_mul_distrib]
    exact (mul_le_mul_of_nonneg_left hb (Finset.prod_nonneg (fun j _ => norm_nonneg _))).trans_eq (mul_comm _ _)
  · push Not at hC
    obtain ⟨j,hj⟩ := hC
    have hz : (List.ofFn (fun j => A j*C j)).prod=0 := by
      apply List.prod_eq_zero
      exact List.mem_ofFn.mpr ⟨j,by simp [hj]⟩
    rw [hz,Matrix.trace_zero,norm_zero]
    exact Finset.prod_nonneg fun j _ => mul_nonneg (schatten_nonneg m _) (norm_nonneg _)

lemma matrix_trace_holder_mixed_list (L : List (Matrix n n ℂ × Matrix n n ℂ))
    (hL : 0 < L.length) :
    ‖Matrix.trace (L.map (fun d => d.1*d.2)).prod‖ ≤
      (L.map (fun d => schatten L.length d.1*‖d.2‖)).prod := by
  have hh := matrix_trace_holder_mixed hL (fun j => (L.get j).1) (fun j => (L.get j).2)
  rw [← List.prod_ofFn] at hh
  have h₁ : List.ofFn (fun j => (L.get j).1*(L.get j).2) = L.map (fun d => d.1*d.2) := by
    simpa only [List.ofFn_get] using List.ofFn_comp' L.get (fun d => d.1*d.2)
  have h₂ : List.ofFn (fun j => schatten L.length (L.get j).1*‖(L.get j).2‖) =
      L.map (fun d => schatten L.length d.1*‖d.2‖) := by
    simpa only [List.ofFn_get] using List.ofFn_comp' L.get (fun d => schatten L.length d.1*‖d.2‖)
  rwa [h₁,h₂] at hh

/- Right ideal inequality for the exact even Schatten norm. -/
theorem schatten_even_mul_right (q : ℕ) (hq : 0 < q) (A C : Matrix n n ℂ) :
    schatten (2*q) (A*C) ≤ schatten (2*q) A * ‖C‖ := by
  let L : List (Matrix n n ℂ × Matrix n n ℂ) :=
    (List.replicate q [(A.conjTranspose,1),(A,C*C.conjTranspose)]).flatten
  have hl : L.length=2*q := by simp [L,List.length_flatten]; omega
  have hh := matrix_trace_holder_mixed_list L (by rw [hl]; omega)
  have hp : (L.map (fun d => d.1*d.2)).prod = (A.conjTranspose*A*(C*C.conjTranspose))^q := by
    simp [L,List.map_flatten,List.prod_flatten,mul_assoc]
  have ht' : Matrix.trace (((A*C).conjTranspose*(A*C))^q) =
      Matrix.trace ((A.conjTranspose*A*(C*C.conjTranspose))^q) := by
    rw [Matrix.conjTranspose_mul]
    have he : C.conjTranspose*A.conjTranspose*(A*C)=C.conjTranspose*(A.conjTranspose*A*C) := by simp only [mul_assoc]
    rw [he,trace_mul_pow_comm]
    simp only [mul_assoc]
  have hn : ‖C*C.conjTranspose‖=‖C‖^2 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self C.conjTranspose
    simpa only [Matrix.conjTranspose_conjTranspose,Matrix.l2_opNorm_conjTranspose,pow_two] using h
  have hr : (L.map (fun d => schatten L.length d.1 * ‖d.2‖)).prod =
      (schatten (2*q) A*‖C‖)^(2*q) := by
    rw [hl]
    simp only [L,List.map_flatten,List.map_replicate,List.map_cons,List.map_nil,
      List.prod_flatten,List.prod_replicate,List.prod_cons,List.prod_nil,
      schatten_adjoint_even,norm_one,mul_one,hn]
    rw [pow_mul]
    congr 1
    ring
  rw [hp,← ht',trace_moment_norm,hr,← schatten_pow _ (by omega)] at hh
  exact (pow_le_pow_iff_left₀ (schatten_nonneg _ _) (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _)) (by omega)).mp hh

end CoordinateSweeps.TraceHolder

namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

lemma norm_le_schatten (m : ℕ) (hm : 0 < m) (A : Matrix n n ℂ) :
    ‖A‖ ≤ schatten m A := by
  by_cases hA : A=0
  · rw [hA,norm_zero]
    exact schatten_nonneg _ _
  · let d := fun i => singular A i / schatten m A
    let B := leftFrame A*Matrix.diagonal (fun i => (d i : ℂ))*(rightBasis A : Matrix n n ℂ).conjTranspose
    have hb : ‖B‖ ≤ 1 := norm_mul_diag_mul_le_one _ _ _ (leftFrame_norm_le A)
      (rightBasis_star_norm_le A) (fun i => by
        simpa only [d,Complex.norm_real,Real.norm_of_nonneg (normalized_singular_le m hm A hA i).1] using
          (normalized_singular_le m hm A hA i).2)
    have he : A=(schatten m A : ℂ) • B := (normalized_polar m hm A hA).symm
    calc
      ‖A‖ = schatten m A * ‖B‖ := by
        conv_lhs => rw [he,norm_smul]
        rw [Complex.norm_real,Real.norm_of_nonneg (schatten_nonneg _ _)]
      _ ≤ schatten m A := mul_le_of_le_one_right (schatten_nonneg m A) hb

lemma schatten_even_mul_left (q : ℕ) (hq : 0 < q) (A C : Matrix n n ℂ) :
    schatten (2*q) (A*C) ≤ ‖A‖ * schatten (2*q) C := by
  have hh := schatten_even_mul_right q hq C.conjTranspose A.conjTranspose
  rw [← Matrix.conjTranspose_mul,schatten_adjoint_even,schatten_adjoint_even,
    Matrix.l2_opNorm_conjTranspose] at hh
  exact hh.trans_eq (mul_comm _ _)

/- The exact three factor inequality used by06:eq20. -/
theorem schatten_even_three (q : ℕ) (hq : 0 < q) (A B C : Matrix n n ℂ) :
    schatten (2*q) (A*B*C) ≤ schatten (2*q) A * ‖B‖ * schatten (2*q) C := by
  calc
    _ ≤ schatten (2*q) (A*B)*‖C‖ := schatten_even_mul_right q hq _ _
    _ ≤ (schatten (2*q) A*‖B‖)*schatten (2*q) C :=
      mul_le_mul (schatten_even_mul_right q hq _ _) (norm_le_schatten _ (by omega) C)
        (norm_nonneg _) (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _))

lemma schatten_even_smul_le (q : ℕ) (hq : 0 < q) (c : ℂ) (A : Matrix n n ℂ) :
    schatten (2*q) (c • A) ≤ ‖c‖ * schatten (2*q) A := by
  have hh := schatten_even_mul_left q hq (c • (1 : Matrix n n ℂ)) A
  simpa only [Matrix.smul_mul,one_mul,norm_smul,norm_one,mul_one] using hh

end CoordinateSweeps.TraceHolder
namespace CoordinateSweeps.TraceHolder
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

omit [Nonempty n] in
lemma projector_norm_le (P : Matrix n n ℂ) (hP : P.IsHermitian) (hP2 : P*P=P) :
    ‖P‖ ≤ 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP.eq,hP2] at hh
  nlinarith [norm_nonneg P]

/- Exact resolution-of-two-subgroups inequality used in source06:eq20. No
orthogonality or occurrence is silently supplied: identity and idempotence
are explicit algebraic premises discharged by the genuine type resolution. -/
theorem row_column_schatten {I J : Type*} [Fintype I] [Fintype J]
    (q : ℕ) (hq : 0 < q) (PR : I → Matrix n n ℂ) (PC : J → Matrix n n ℂ)
    (hR : ∑ i, PR i=1) (hC : ∑ j, PC j=1)
    (hR2 : ∀ i, PR i*PR i=PR i) (hC2 : ∀ j, PC j*PC j=PC j)
    (P X Y : Matrix n n ℂ) :
    schatten (2*q) (Y*P*X) ≤
      ∑ ij : J × I, schatten (2*q) (Y*PC ij.1)*
        ‖PC ij.1*P*PR ij.2‖*schatten (2*q) (PR ij.2*X) := by
  have he : (∑ ij : J × I, (Y*PC ij.1)*(PC ij.1*P*PR ij.2)*(PR ij.2*X))=Y*P*X := by
    simp only [Fintype.sum_prod_type]
    have hterm (j : J) (i : I) :
        (Y*PC j)*(PC j*P*PR i)*(PR i*X)=Y*PC j*P*PR i*X := by
      calc
        _ = Y*(PC j*PC j)*P*(PR i*PR i)*X := by simp only [mul_assoc]
        _ = _ := by rw [hC2,hR2]
    simp only [hterm]
    simp only [← Matrix.sum_mul,← Matrix.mul_sum,hR,hC,mul_one]
  calc
    _ = schatten (2*q) (∑ ij : J × I, (Y*PC ij.1)*(PC ij.1*P*PR ij.2)*(PR ij.2*X)) := by rw [he]
    _ ≤ ∑ ij : J × I, schatten (2*q) ((Y*PC ij.1)*(PC ij.1*P*PR ij.2)*(PR ij.2*X)) :=
      schatten_even_sum_le q hq _
    _ ≤ _ := Finset.sum_le_sum (fun ij _ => schatten_even_three q hq _ _ _)

lemma contraction_power_from_overlap {t B c : ℝ} (q : ℕ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hc : 0 ≤ c) (hcq : c ≤ q)
    (hB : t^2 ≤ Real.exp B) :
    t^(2*q) ≤ Real.exp (c*B) := by
  calc
    _ = (t^2)^q := pow_mul t 2 q
    _ = (t^2)^(q : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (t^2)^c := Real.rpow_le_rpow_of_exponent_ge' (sq_nonneg t)
      (pow_le_one₀ ht ht1) hc hcq
    _ ≤ (Real.exp B)^c := Real.rpow_le_rpow (sq_nonneg t) hB hc
    _ = _ := by rw [← Real.exp_mul]; congr 1; ring

/- Algebraic cancellation of subgroup dimensions, preserving the absolute
(not normalized) even moment. This is the quantitative core of06:eq21. -/
theorem row_column_moment {I J : Type*} [Fintype I] [Fintype J]
    (q : ℕ) (hq : 0 < q) (PR : I → Matrix n n ℂ) (PC : J → Matrix n n ℂ)
    (hR : ∑ i, PR i=1) (hC : ∑ j, PC j=1)
    (hR2 : ∀ i, PR i*PR i=PR i) (hC2 : ∀ j, PC j*PC j=PC j)
    (P X Y : Matrix n n ℂ) (FR : I → ℝ) (FC : J → ℝ) (F A B c : ℝ)
    (hc : 0 ≤ c) (hcq : c ≤ q)
    (hchild : ∀ i j,
      (Matrix.trace (((PR i*X).conjTranspose*(PR i*X))^q)).re *
        (Matrix.trace (((Y*PC j).conjTranspose*(Y*PC j))^q)).re ≤
          Real.exp (-c*(FR i+FC j)+A))
    (hoverlap : ∀ i j, ‖PC j*P*PR i‖^2 ≤ Real.exp (FR i+FC j-F+B))
    (hcontract : ∀ i j, ‖PC j*P*PR i‖ ≤ 1) :
    (Matrix.trace (((Y*P*X).conjTranspose*(Y*P*X))^q)).re ≤
      ((Fintype.card I*Fintype.card J : ℕ) : ℝ)^(2*q)*Real.exp (-c*F+A+c*B) := by
  let E := Real.exp ((-c*F+A+c*B)/(2*q : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hEq : E^(2*q)=Real.exp (-c*F+A+c*B) := by
    dsimp [E]
    rw [← Real.exp_nat_mul]
    congr 1
    have hq0 : (2*q : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have hb (j : J) (i : I) :
      schatten (2*q) (Y*PC j)*‖PC j*P*PR i‖*schatten (2*q) (PR i*X) ≤ E := by
    apply (pow_le_pow_iff_left₀ (mul_nonneg (mul_nonneg (schatten_nonneg _ _) (norm_nonneg _)) (schatten_nonneg _ _)) hE (show 2*q ≠ 0 by omega)).mp
    rw [hEq]
    simp only [mul_pow,schatten_even_pow q hq]
    have hch := hchild i j
    have hp := contraction_power_from_overlap q (norm_nonneg _) (hcontract i j) hc hcq (hoverlap i j)
    calc
      _ = ((Matrix.trace (((PR i*X).conjTranspose*(PR i*X))^q)).re *
            (Matrix.trace (((Y*PC j).conjTranspose*(Y*PC j))^q)).re) *
                ‖PC j*P*PR i‖^(2*q) := by ring
      _ ≤ Real.exp (-c*(FR i+FC j)+A)*Real.exp (c*(FR i+FC j-F+B)) :=
        mul_le_mul hch hp (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hs : schatten (2*q) (Y*P*X) ≤ (Fintype.card I*Fintype.card J : ℕ)*E := by
    apply (row_column_schatten q hq PR PC hR hC hR2 hC2 P X Y).trans
    calc
      _ ≤ ∑ _ : J × I, E := Finset.sum_le_sum (fun ij _ => hb ij.1 ij.2)
      _ = _ := by simp [Fintype.card_prod,Nat.mul_comm]
  have hp := pow_le_pow_left₀ (schatten_nonneg _ _) hs (2*q)
  rw [schatten_even_pow q hq,mul_pow,hEq] at hp
  exact hp

end CoordinateSweeps.TraceHolder

end
end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
