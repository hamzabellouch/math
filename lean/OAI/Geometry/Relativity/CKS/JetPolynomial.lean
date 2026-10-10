import OAI.Geometry.Relativity.CKS.ScalarJetCalculus

namespace OAI

noncomputable section
namespace CKSAngularGeometry
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
  ext a b <;> simp [productJet,constantJet]
  ring
lemma productJet_constant_left (f : ScalarJet) (c : ℝ) : productJet (constantJet c) f = c • f := by
  ext a b <;> simp [productJet,constantJet]
lemma constantJet_smul (c d : ℝ) : constantJet (c*d) = c • constantJet d := by
  ext a b <;> simp [constantJet]
lemma constantJet_add (c d : ℝ) : constantJet (c+d) = constantJet c+constantJet d := by
  ext a b <;> simp [constantJet]
lemma reciprocalJet_one : reciprocalJet (constantJet 1) = constantJet 1 := by
  ext a b <;> simp [reciprocalJet,constantJet]

def massNumeratorJet (z : ℝ) (D T V : ScalarJet) : ScalarJet :=
  (1+z^2) • V+(2:ℝ) • T-(2*(1+z^2)) • D+
    z^3 • (productJet T T+(2:ℝ) • productJet T V-(1+z^2) • productJet D D)+
    z^6 • productJet (productJet T T) V

def normalizedMassJet (z : ℝ) (D T V : ScalarJet) : ScalarJet :=
  (1/2:ℝ) • productJet (massNumeratorJet z D T V)
    (reciprocalJet (constantJet 1+z^3 • V))

lemma massNumeratorJet_smooth : ContDiff ℝ ∞
    (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => massNumeratorJet j.1 j.2.1 j.2.2.1 j.2.2.2) := by
  have hTT : ContDiff ℝ ∞ (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => productJet j.2.2.1 j.2.2.1) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => (j.2.2.1,j.2.2.1)))
  have hTV : ContDiff ℝ ∞ (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => productJet j.2.2.1 j.2.2.2) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => (j.2.2.1,j.2.2.2)))
  have hDD : ContDiff ℝ ∞ (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => productJet j.2.1 j.2.1) :=
    productJet_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => (j.2.1,j.2.1)))
  have hTTV : ContDiff ℝ ∞ (fun j : ℝ × ScalarJet × ScalarJet × ScalarJet => productJet (productJet j.2.2.1 j.2.2.1) j.2.2.2) :=
    productJet_smooth.comp (hTT.prodMk (by fun_prop))
  unfold massNumeratorJet
  fun_prop

lemma normalizedMassJet_smooth {j : ℝ × ScalarJet × ScalarJet × ScalarJet}
    (h0 : (constantJet 1+j.1^3 • j.2.2.2).1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun k : ℝ × ScalarJet × ScalarJet × ScalarJet =>
      normalizedMassJet k.1 k.2.1 k.2.2.1 k.2.2.2) j := by
  have hi := (reciprocalJet_smooth h0).comp j
    (by fun_prop : ContDiffAt ℝ ∞ (fun k : ℝ × ScalarJet × ScalarJet × ScalarJet => constantJet 1+k.1^3 • k.2.2.2) j)
  exact (productJet_smooth.contDiffAt.comp j (massNumeratorJet_smooth.contDiffAt.prodMk hi)).const_smul _

lemma normalizedMassJet_zero (D T V : ScalarJet) :
    normalizedMassJet 0 D T V = (1/2:ℝ) • (V+(2:ℝ) • T-(2:ℝ) • D) := by
  simp only [normalizedMassJet,massNumeratorJet,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_pow (by norm_num : (3:ℕ) ≠ 0),zero_pow (by norm_num : (6:ℕ) ≠ 0),
    add_zero,zero_smul,mul_one,one_smul,reciprocalJet_one,productJet_constant_right]

theorem exact_mass_cancellation {z D T V : ℝ} (hz : z ≠ 0) (hv : 1+z^3*V ≠ 0) :
    (z^2+(1+z^3*T)^2-(1+z^2)*(1+z^3*D)^2/(1+z^3*V))/(2*z^3) =
      ((1+z^2)*V+2*T-2*(1+z^2)*D+
        z^3*(T^2+2*T*V-(1+z^2)*D^2)+z^6*T^2*V)/(2*(1+z^3*V)) := by
  field_simp
  ring

end
end CKSAngularGeometry

end

end OAI
