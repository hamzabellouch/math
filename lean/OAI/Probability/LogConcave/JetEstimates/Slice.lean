import Mathlib
import OAI.Probability.LogConcave.JetEstimates.TensorTerm
import OAI.Probability.LogConcave.Complexity.PolynomialBudget
import OAI.Probability.LogConcave.Sampling.FinSnocSlots

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory TensorExpression
open scoped Classical BigOperators ENNReal NNReal

namespace TensorAtom
variable {S : Type} [Fintype S]
def slice {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ) :
    (S → Fin d) → Point d → ℝ := fun c y => A.eval F x r L c (ρ,y)

omit [Fintype S] in
lemma slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (c : S → Fin d) : PolySmooth (A.slice F x r ρ ((lam:ℝ)*r) c) := by
  change PolySmooth (fun y => A.expression.jointEval F x r ((lam:ℝ)*r) (c ∘ A.labels) (ρ,y))
  rw [TensorExpression.jointEval_slice hF x hr hlam hl h0 h1]
  exact TensorExpression.eval_polySmooth (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression _

def spatialBound {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) : Point d → ℝ :=
  spatialEnvelope (A.expression.eval (physicalBase F x r ρ L) (interpolationPotential F x r ρ)) j

omit [Fintype S] in
lemma spatialBound_nonneg {d : ℕ} (A : TensorAtom S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) (y : Point d) : 0≤A.spatialBound F x r ρ L j y :=
  spatialEnvelope_nonneg _ _ _

omit [Fintype S] in
lemma spatialBound_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (j : ℕ) : Measurable (A.spatialBound F x r ρ ((lam:ℝ)*r) j) :=
  spatialEnvelope_measurable _ (TensorExpression.eval_polySmooth
    (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression) j

lemma spatialBound_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorAtom S) (j : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y)
      (A.spatialBound F x r ρ ((lam:ℝ)*r) j y) := by
  let V := A.expression.eval (physicalBase F x r ρ ((lam:ℝ)*r)) (interpolationPotential F x r ρ)
  have hs := TensorExpression.eval_polySmooth (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression
  have he : A.slice F x r ρ ((lam:ℝ)*r)=fun c => V (c ∘ A.labels) := by
    funext c
    exact A.expression.jointEval_slice hF x hr hlam hl h0 h1 _
  rw [he]
  exact spatialTensor_allSplit_relabel V (fun c => (hs c).smooth) A.labels
    (Equiv.refl (Fin j)) _ _ (by simp) y _ (TensorEnergy.allSplitBound_envelope _)

omit [Fintype S] in
lemma spatialBound_Lp {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorAtom S) (j : ℕ) {p : ℝ≥0∞} (hpf : p≠⊤) :
    eLpNorm (A.spatialBound F x r ρ ((lam:ℝ)*r) j) p (interpolationLaw F x r ρ)≤
      ((4*(A.expression.profileConstant:ℝ≥0∞))*ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^
        (A.expression.profileConstant*(j+1))*
      ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(A.expression.weight+j) := by
  let : IsProbabilityMeasure (interpolationLaw F x r ρ) := interpolationLaw_probability hF x hr.le (by linarith) ρ
  exact TameAt.eLpNorm (TensorExpression.eval_polySmooth
    (physicalBase_polySmooth hF x hr hlam hl h0 h1)
    (interpolationPotential_polySmooth hF x hr hlam hl h0 h1) A.expression)
    (A.expression.physical_tame hF x hr hlam hl h0 h1 hd) j hpf
end TensorAtom

namespace TensorEnergy
lemma AllSplitBound.abs_const_mul {S : Type} [Fintype S] {d : ℕ}
    {T : (S → Fin d) → ℝ} {M : ℝ} (h : AllSplitBound T M) (c : ℝ) :
    AllSplitBound (fun a => c*T a) (|c| * M) := by
  intro I O _ _ _ _ _ _ e
  convert (h.const_mul c) I O e using 1
  simp only [mul_pow,sq_abs]
end TensorEnergy

lemma spatialTensor_const_mul {S : Type} {d j : ℕ}
    (V : (S → Fin d) → Point d → ℝ) (hV : ∀c,ContDiff ℝ (⊤:ℕ∞) (V c))
    (a : ℝ) (y : Point d) :
    spatialTensor (fun c z => a*V c z) (List.finRange j) y=
      fun c => a*spatialTensor V (List.finRange j) y c := by
  funext c
  exact congrFun (JetCalculus.jet_const_mul (hV _) _ _ a) y

lemma spatialTensor_sum {S I : Type} [Fintype I] {d j : ℕ}
    (V : I → (S → Fin d) → Point d → ℝ) (hV : ∀i c,ContDiff ℝ (⊤:ℕ∞) (V i c))
    (y : Point d) :
    spatialTensor (fun c z => ∑i,V i c z) (List.finRange j) y=
      fun c => ∑i,spatialTensor (V i) (List.finRange j) y c := by
  funext c
  exact congrFun (JetCalculus.jet_sum Finset.univ (fun i _ => hV i _) _ _) y

namespace TensorSum
variable {S : Type} [Fintype S]
def slice {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d) (r ρ L : ℝ) :
    (S → Fin d) → Point d → ℝ := fun c y => A.eval F x r L c (ρ,y)

def spatialBound {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) : Point d → ℝ := fun y =>
  ∑i,polynomialBudget (A.term i).coefficient*(A.term i).atom.spatialBound F x r ρ L j y

omit [Fintype S] in
lemma spatialBound_nonneg {d : ℕ} (A : TensorSum S) (F : Point d → ℝ) (x : Point d)
    (r ρ L : ℝ) (j : ℕ) (y : Point d) : 0≤A.spatialBound F x r ρ L j y :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (polynomialBudget_nonneg _) (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _))

omit [Fintype S] in
lemma spatialBound_measurable {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum S) (j : ℕ) : Measurable (A.spatialBound F x r ρ ((lam:ℝ)*r) j) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul
    ((A.term i).atom.spatialBound_measurable hF x hr hlam hl h0 h1 j))

omit [Fintype S] in
lemma slice_polySmooth {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum S) (c : S → Fin d) : PolySmooth (A.slice F x r ρ ((lam:ℝ)*r) c) :=
by
  change PolySmooth (fun z => ∑i, ((r*((lam:ℝ)*r))^(A.term i).power*
    (A.term i).coefficient.eval ρ)*(A.term i).atom.slice F x r ρ ((lam:ℝ)*r) c z)
  exact PolySmooth.sum Finset.univ (fun i _ =>
    (PolySmooth.const _).mul ((A.term i).atom.slice_polySmooth hF x hr hlam hl h0 h1 c))

lemma spatialBound_allSplit {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (A : TensorSum S) (j : ℕ) (y : Point d) :
    TensorEnergy.AllSplitBound (spatialTensor (A.slice F x r ρ ((lam:ℝ)*r)) (List.finRange j) y)
      (A.spatialBound F x r ρ ((lam:ℝ)*r) j y) := by
  let L := (lam:ℝ)*r
  let a := fun i => (r*L)^(A.term i).power*(A.term i).coefficient.eval ρ
  have hs (i : A.index) (c : S → Fin d) := (A.term i).atom.slice_polySmooth hF x hr hlam hl h0 h1 c
  have he : A.slice F x r ρ L=fun c z => ∑i,a i*(A.term i).atom.slice F x r ρ L c z := rfl
  rw [he,spatialTensor_sum _ (fun i c => contDiff_const.mul (hs i c).smooth)]
  simp_rw [spatialTensor_const_mul _ (fun c => (hs _ c).smooth)]
  apply TensorEnergy.AllSplitBound.finite_sum
  · intro i; exact mul_nonneg (polynomialBudget_nonneg _) (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _)
  · intro i
    have ht := (A.term i).atom.spatialBound_allSplit hF x hr hlam hl h0 h1 j y
    apply (TensorEnergy.AllSplitBound.abs_const_mul ht (a i)).mono (mul_nonneg (abs_nonneg _) (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _))
    apply mul_le_mul_of_nonneg_right _ (TensorAtom.spatialBound_nonneg _ _ _ _ _ _ _ _)
    exact scaledCoefficient_bound _ _ (by dsimp [L]; positivity)
      (by change r*((lam:ℝ)*r)≤1; nlinarith [hl]) h0 h1.le
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open scoped Classical BigOperators ENNReal NNReal

namespace TensorSum
variable {S : Type} [Fintype S]

def momentBudget (A : TensorSum S) (d j : ℕ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ∑i,ENNReal.ofReal (polynomialBudget (A.term i).coefficient)*
    ((4*((A.term i).atom.expression.profileConstant:ℝ≥0∞))*
      ENNReal.ofReal (p.toReal+j+Real.log ((d:ℝ)+1)+1))^
        ((A.term i).atom.expression.profileConstant*(j+1))

omit [Fintype S] in
lemma momentBudget_ne_top (A : TensorSum S) (d j : ℕ) (p : ℝ≥0∞) :
    A.momentBudget d j p≠⊤ := by
  apply ne_of_lt
  apply ENNReal.sum_lt_top.mpr
  intro i _
  apply ENNReal.mul_lt_top (ENNReal.ofReal_lt_top)
  exact ENNReal.pow_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (ENNReal.natCast_lt_top _)) ENNReal.ofReal_lt_top)

omit [Fintype S] in
lemma spatialBound_Lp {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0 < r)
    (hlam : 0 < lam) (hl : (lam:ℝ)*r^2≤1/2) (h0 : 0≤ρ) (h1 : ρ<1)
    (hd : 1≤d) (A : TensorSum S) {w : ℕ} (hw : A.weightLE w)
    (j : ℕ) {p : ℝ≥0∞} (hp : 1≤p) (hpf : p≠⊤) :
    eLpNorm (A.spatialBound F x r ρ ((lam:ℝ)*r) j) p (interpolationLaw F x r ρ)≤
      A.momentBudget d j p*ENNReal.ofReal ((Real.sqrt (1-ρ^2))⁻¹)^(w+j) := by
  let μ := interpolationLaw F x r ρ
  let V := fun i => (A.term i).atom.spatialBound F x r ρ ((lam:ℝ)*r) j
  let a := fun i => polynomialBudget (A.term i).coefficient
  have he : A.spatialBound F x r ρ ((lam:ℝ)*r) j=∑i,a i • V i := by
    funext y
    simp only [spatialBound,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,V,a]
  rw [he]
  apply (eLpNorm_sum_le (μ:=μ) (s:=Finset.univ) (f:=fun index => a index • V index) hp).trans
  rw [momentBudget,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [eLpNorm_const_smul]
  have ha : ‖a i‖ₑ=ENNReal.ofReal (a i) := by
    rw [Real.enorm_eq_ofReal_abs,abs_of_nonneg (polynomialBudget_nonneg _)]
  rw [ha,mul_assoc]
  apply mul_le_mul' le_rfl
  apply ((A.term i).atom.spatialBound_Lp hF x hr hlam hl h0 h1 hd j hpf).trans
  apply mul_le_mul' le_rfl
  apply pow_le_pow_right'
  · apply ENNReal.one_le_ofReal.mpr
    have hs0 : 0 < Real.sqrt (1-ρ^2) := Real.sqrt_pos.2 (by nlinarith)
    have hs1 : Real.sqrt (1-ρ^2)≤1 := by
      exact (Real.sqrt_le_iff).2 ⟨by norm_num,by nlinarith [sq_nonneg ρ]⟩
    exact (one_le_inv₀ hs0).mpr hs1
  · exact Nat.add_le_add_right (hw i) j
end TensorSum
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open scoped Classical BigOperators

namespace TensorEnergy
variable {I J S : Type} [Fintype I] [Fintype J] [Fintype S]

lemma Bound.frobeniusSquared_row {A : I → J → ℝ} {C : ℝ} (h : Bound A C) (hC : 0≤C) :
    ∑i,∑j,(A i j)^2≤Fintype.card I*C := by
  have hb (i : I) : ∑j,(A i j)^2≤C := by
    have hh := h.transpose hC (fun k => if k=i then 1 else 0)
    simpa using hh
  exact (Finset.sum_le_sum (fun i _ => hb i)).trans_eq (by simp)

lemma AllSplitBound.frobeniusSquared {d : ℕ} {T : (S → Fin d) → ℝ} {M : ℝ}
    (h : AllSplitBound T M) [Nonempty I] (e : S ≃ I ⊕ Unit) :
    ∑c,(T c)^2≤d*M^2 := by
  let A : (Unit → Fin d) → (I → Fin d) → ℝ :=
    fun o i => T (fun s => Sum.elim i o (e s))
  have hb : Bound A (M^2) := h I Unit e
  have he : (∑c,(T c)^2)=∑o : Unit → Fin d,∑i : I → Fin d,(A o i)^2 := by
    let ec : ((Unit → Fin d) × (I → Fin d)) ≃ (S → Fin d) :=
      ((Equiv.prodComm _ _).trans (Equiv.sumArrowEquivProdArrow I Unit (Fin d)).symm).trans
        (Equiv.arrowCongr e.symm (Equiv.refl (Fin d)))
    have hh := Equiv.sum_comp ec (fun c => (T c)^2)
    rw [Fintype.sum_prod_type] at hh
    exact hh.symm
  rw [he]
  simpa using hb.frobeniusSquared_row (sq_nonneg M)
end TensorEnergy
end LogConcaveSampling

end

end

end

end OAI
