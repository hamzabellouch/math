import OAI.Geometry.Relativity.CKS.JetPolynomial
import OAI.Geometry.Relativity.CKS.CollarShiftJet
import OAI.Geometry.Relativity.CKS.MixedThreeJets

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma productJet_add_left (f g h : ScalarJet) : productJet (f+g) h = productJet f h+productJet g h := by
  apply Prod.ext
  · change (f.1+g.1)*h.1 = (f.1*h.1)+(g.1*h.1)
    ring
  apply Prod.ext
  · funext a
    change (f.1+g.1)*h.2.1 a+h.1*(f.2.1 a+g.2.1 a) = (f.1*h.2.1 a+h.1*f.2.1 a)+(g.1*h.2.1 a+h.1*g.2.1 a)
    ring
  · funext a b
    change (f.1+g.1)*h.2.2 a b+h.1*(f.2.2 a b+g.2.2 a b)+(f.2.1 a+g.2.1 a)*h.2.1 b+h.2.1 a*(f.2.1 b+g.2.1 b) = (f.1*h.2.2 a b+h.1*f.2.2 a b+f.2.1 a*h.2.1 b+h.2.1 a*f.2.1 b)+(g.1*h.2.2 a b+h.1*g.2.2 a b+g.2.1 a*h.2.1 b+h.2.1 a*g.2.1 b)
    ring

lemma productJet_add_right (f g h : ScalarJet) : productJet f (g+h) = productJet f g+productJet f h := by
  apply Prod.ext
  · change f.1*(g.1+h.1) = (f.1*g.1)+(f.1*h.1)
    ring
  apply Prod.ext
  · funext a
    change f.1*(g.2.1 a+h.2.1 a)+(g.1+h.1)*f.2.1 a = (f.1*g.2.1 a+g.1*f.2.1 a)+(f.1*h.2.1 a+h.1*f.2.1 a)
    ring
  · funext a b
    change f.1*(g.2.2 a b+h.2.2 a b)+(g.1+h.1)*f.2.2 a b+f.2.1 a*(g.2.1 b+h.2.1 b)+(g.2.1 a+h.2.1 a)*f.2.1 b = (f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)+(f.1*h.2.2 a b+h.1*f.2.2 a b+f.2.1 a*h.2.1 b+h.2.1 a*f.2.1 b)
    ring

lemma productJet_smul_left (c : ℝ) (f g : ScalarJet) : productJet (c • f) g = c • productJet f g := by
  apply Prod.ext
  · change (c*f.1)*g.1 = c*(f.1*g.1)
    ring
  apply Prod.ext
  · funext a
    change (c*f.1)*g.2.1 a+g.1*(c*f.2.1 a) = c*(f.1*g.2.1 a+g.1*f.2.1 a)
    ring
  · funext a b
    change (c*f.1)*g.2.2 a b+g.1*(c*f.2.2 a b)+(c*f.2.1 a)*g.2.1 b+g.2.1 a*(c*f.2.1 b) = c*(f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)
    ring

lemma productJet_smul_right (c : ℝ) (f g : ScalarJet) : productJet f (c • g) = c • productJet f g := by
  apply Prod.ext
  · change f.1*(c*g.1) = c*(f.1*g.1)
    ring
  apply Prod.ext
  · funext a
    change f.1*(c*g.2.1 a)+(c*g.1)*f.2.1 a = c*(f.1*g.2.1 a+g.1*f.2.1 a)
    ring
  · funext a b
    change f.1*(c*g.2.2 a b)+(c*g.1)*f.2.2 a b+f.2.1 a*(c*g.2.1 b)+(c*g.2.1 a)*f.2.1 b = c*(f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)
    ring

lemma productJet_sub_left (f g h : ScalarJet) : productJet (f-g) h = productJet f h-productJet g h := by
  apply Prod.ext
  · change (f.1-g.1)*h.1 = (f.1*h.1)-(g.1*h.1)
    ring
  apply Prod.ext
  · funext a
    change (f.1-g.1)*h.2.1 a+h.1*(f.2.1 a-g.2.1 a) = (f.1*h.2.1 a+h.1*f.2.1 a)-(g.1*h.2.1 a+h.1*g.2.1 a)
    ring
  · funext a b
    change (f.1-g.1)*h.2.2 a b+h.1*(f.2.2 a b-g.2.2 a b)+(f.2.1 a-g.2.1 a)*h.2.1 b+h.2.1 a*(f.2.1 b-g.2.1 b) = (f.1*h.2.2 a b+h.1*f.2.2 a b+f.2.1 a*h.2.1 b+h.2.1 a*f.2.1 b)-(g.1*h.2.2 a b+h.1*g.2.2 a b+g.2.1 a*h.2.1 b+h.2.1 a*g.2.1 b)
    ring

lemma productJet_sub_right (f g h : ScalarJet) : productJet f (g-h) = productJet f g-productJet f h := by
  apply Prod.ext
  · change f.1*(g.1-h.1) = (f.1*g.1)-(f.1*h.1)
    ring
  apply Prod.ext
  · funext a
    change f.1*(g.2.1 a-h.2.1 a)+(g.1-h.1)*f.2.1 a = (f.1*g.2.1 a+g.1*f.2.1 a)-(f.1*h.2.1 a+h.1*f.2.1 a)
    ring
  · funext a b
    change f.1*(g.2.2 a b-h.2.2 a b)+(g.1-h.1)*f.2.2 a b+f.2.1 a*(g.2.1 b-h.2.1 b)+(g.2.1 a-h.2.1 a)*f.2.1 b = (f.1*g.2.2 a b+g.1*f.2.2 a b+f.2.1 a*g.2.1 b+g.2.1 a*f.2.1 b)-(f.1*h.2.2 a b+h.1*f.2.2 a b+f.2.1 a*h.2.1 b+h.2.1 a*f.2.1 b)
    ring
lemma productJet_constant_right (f : ScalarJet) (c : ℝ) : productJet f (constantJet c) = c • f := by
  ext a b <;> simp [productJet,constantJet,mul_comm]
lemma productJet_constant_left (f : ScalarJet) (c : ℝ) : productJet (constantJet c) f = c • f := by
  ext a b <;> simp [productJet,constantJet]
lemma constantJet_smul (c d : ℝ) : constantJet (c*d) = c • constantJet d := by
  ext a b <;> simp [constantJet]
lemma constantJet_add (c d : ℝ) : constantJet (c+d) = constantJet c+constantJet d := by
  ext a b <;> simp [constantJet]
lemma reciprocalJet_one : reciprocalJet (constantJet 1) = constantJet 1 := by
  ext a b <;> simp [reciprocalJet,constantJet]

@[simp] lemma productJet_zero_right (f : ScalarJet) : productJet f 0 = 0 := by
  ext a b <;> simp [productJet]
@[simp] lemma productJet_zero_left (f : ScalarJet) : productJet 0 f = 0 := by
  ext a b <;> simp [productJet]
@[simp] lemma productThreeJet_zero_right (f : ScalarThreeJet) : productThreeJet f 0 = 0 := by
  apply Prod.ext
  · exact productJet_zero_right f.1
  · funext a; simp [productThreeJet]
@[simp] lemma productThreeJet_zero_left (f : ScalarThreeJet) : productThreeJet 0 f = 0 := by
  apply Prod.ext
  · exact productJet_zero_left f.1
  · funext a; simp [productThreeJet]

def powJet (f : ScalarJet) : ℕ → ScalarJet
  | 0 => constantJet 1
  | n+1 => productJet (powJet f n) f

def powThreeJet (f : ScalarThreeJet) : ℕ → ScalarThreeJet
  | 0 => constantThreeJet 1
  | n+1 => productThreeJet (powThreeJet f n) f

@[simp] lemma powJet_zero_succ (n : ℕ) : powJet 0 (n+1) = 0 := by simp [powJet]
@[simp] lemma powThreeJet_zero_succ (n : ℕ) : powThreeJet 0 (n+1) = 0 := by simp [powThreeJet]
lemma powJet_fst (j : ScalarJet) (n : ℕ) : (powJet j n).1 = j.1^n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [powJet,productJet,pow_succ] using congrArg (fun x : ℝ => x*j.1) ih
lemma powThreeJet_fst (j : ScalarThreeJet) (n : ℕ) : (powThreeJet j n).1 = powJet j.1 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change productJet (powThreeJet j n).1 j.1 = productJet (powJet j.1 n) j.1
    rw [ih]

lemma powJet_smooth (n : ℕ) : ContDiff ℝ ∞ (fun j : ScalarJet => powJet j n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact productJet_smooth.comp (ih.prodMk contDiff_id)
lemma powThreeJet_smooth (n : ℕ) : ContDiff ℝ ∞ (fun j : ScalarThreeJet => powThreeJet j n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih => exact productThreeJet_smooth.comp (ih.prodMk contDiff_id)

lemma actualScalarJet_pow {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 2 f x) (n : ℕ) :
    actualScalarJet (fun y => f y^n) x = powJet (actualScalarJet f x) n := by
  induction n with
  | zero => exact actualScalarJet_const 1 x
  | succ n ih => simp only [pow_succ,powJet,actualScalarJet_mul (hf.pow n) hf,ih]
lemma actualThreeJet_pow {f : Point → ℝ} {x : Point} (hf : ContDiffAt ℝ 3 f x) (n : ℕ) :
    actualThreeJet (fun y => f y^n) x = powThreeJet (actualThreeJet f x) n := by
  induction n with
  | zero => exact actualThreeJet_const 1 x
  | succ n ih => simp only [pow_succ,powThreeJet,actualThreeJet_mul (hf.pow n) hf,ih]

section SmoothRules
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[fun_prop] lemma productJet_contDiff {f g : E → ScalarJet} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => productJet (f x) (g x)) := productJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma productJet_contDiffAt {f g : E → ScalarJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => productJet (f y) (g y)) x := productJet_smooth.contDiffAt.comp x (hf.prodMk hg)
@[fun_prop] lemma powJet_contDiff {f : E → ScalarJet} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => powJet (f x) n) := (powJet_smooth n).comp hf
@[fun_prop] lemma powJet_contDiffAt {f : E → ScalarJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ContDiffAt ℝ ∞ (fun y => powJet (f y) n) x := (powJet_smooth n).contDiffAt.comp x hf
@[fun_prop] lemma productThreeJet_contDiff {f g : E → ScalarThreeJet} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => productThreeJet (f x) (g x)) := productThreeJet_smooth.comp (hf.prodMk hg)
@[fun_prop] lemma productThreeJet_contDiffAt {f g : E → ScalarThreeJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ContDiffAt ℝ ∞ (fun y => productThreeJet (f y) (g y)) x := productThreeJet_smooth.contDiffAt.comp x (hf.prodMk hg)
@[fun_prop] lemma powThreeJet_contDiff {f : E → ScalarThreeJet} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => powThreeJet (f x) n) := (powThreeJet_smooth n).comp hf
@[fun_prop] lemma powThreeJet_contDiffAt {f : E → ScalarThreeJet} {x : E} (hf : ContDiffAt ℝ ∞ f x) (n : ℕ) :
    ContDiffAt ℝ ∞ (fun y => powThreeJet (f y) n) x := (powThreeJet_smooth n).contDiffAt.comp x hf
end SmoothRules

def massNumeratorJet (z D T V : ScalarJet) : ScalarJet :=
  productJet (constantJet 1+powJet z 2) V+(2:ℝ) • T-
    (2:ℝ) • productJet (constantJet 1+powJet z 2) D+
    productJet (powJet z 3) (productJet T T+(2:ℝ) • productJet T V-
      productJet (constantJet 1+powJet z 2) (productJet D D))+
    productJet (powJet z 6) (productJet (productJet T T) V)
def normalizedMassJet (z D T V : ScalarJet) : ScalarJet :=
  (1/2:ℝ) • productJet (massNumeratorJet z D T V)
    (reciprocalJet (constantJet 1+productJet (powJet z 3) V))

lemma massNumeratorJet_smooth : ContDiff ℝ ∞
    (fun j : ScalarJet × ScalarJet × ScalarJet × ScalarJet => massNumeratorJet j.1 j.2.1 j.2.2.1 j.2.2.2) := by
  unfold massNumeratorJet
  fun_prop
lemma normalizedMassJet_smooth {j : ScalarJet × ScalarJet × ScalarJet × ScalarJet}
    (h0 : (constantJet 1+productJet (powJet j.1 3) j.2.2.2).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun k : ScalarJet × ScalarJet × ScalarJet × ScalarJet =>
      normalizedMassJet k.1 k.2.1 k.2.2.1 k.2.2.2) j := by
  have hi := (reciprocalJet_smooth h0).comp j
    (by fun_prop : ContDiffAt ℝ ∞ (fun k : ScalarJet × ScalarJet × ScalarJet × ScalarJet =>
      constantJet 1+productJet (powJet k.1 3) k.2.2.2) j)
  exact (productJet_smooth.contDiffAt.comp j (massNumeratorJet_smooth.contDiffAt.prodMk hi)).const_smul _
lemma normalizedMassJet_zero (D T V : ScalarJet) :
    normalizedMassJet 0 D T V = (1/2:ℝ) • (V+(2:ℝ) • T-(2:ℝ) • D) := by
  simp [normalizedMassJet,massNumeratorJet,productJet_constant_left,productJet_constant_right,reciprocalJet_one]

end
end CKSMixedGeometry

end

end OAI
