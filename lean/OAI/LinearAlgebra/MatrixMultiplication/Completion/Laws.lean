import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexEntropyContinuity

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]

def mixture (p : FiniteLaw B) (q : B → FiniteLaw A) : FiniteLaw A :=
  (p.joint q).map Prod.snd

theorem mixture_mass (p : FiniteLaw B) (q : B → FiniteLaw A) (a : A) :
    (mixture p q).mass a = ∑ b, p.mass b * (q b).mass a := by
  classical
  simp [mixture, FiniteLaw.map_mass, FiniteLaw.joint, Fintype.sum_prod_type]

theorem mixture_map_mass (p : FiniteLaw B) (q : B → FiniteLaw A)
    (f : A → X) (x : X) :
    ((mixture p q).map f).mass x = ∑ b, p.mass b * ((q b).map f).mass x := by
  classical
  simp only [FiniteLaw.map_mass, mixture_mass]
  calc
    (∑ a, if f a = x then ∑ b, p.mass b * (q b).mass a else 0) =
        ∑ a, ∑ b, if f a = x then p.mass b * (q b).mass a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = ∑ b, ∑ a, if f a = x then p.mass b * (q b).mass a else 0 :=
      Finset.sum_comm
    _ = ∑ b, p.mass b * ∑ a, if f a = x then (q b).mass a else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp

theorem mixture_common_marginal (p : FiniteLaw B) (q : B → FiniteLaw A)
    (f : A → X) (r : FiniteLaw X)
    (hq : ∀ b x, ((q b).map f).mass x = r.mass x) (x : X) :
    ((mixture p q).map f).mass x = r.mass x := by
  rw [mixture_map_mass]
  simp_rw [hq]
  rw [← Finset.sum_mul, p.total, one_mul]

theorem joint_common_marginal (p : FiniteLaw B) (q : B → FiniteLaw A)
    (f : A → X) (r : FiniteLaw X)
    (hq : ∀ b x, ((q b).map f).mass x = r.mass x) (b : B) (x : X) :
    ((p.joint q).map (fun ba => (ba.1, f ba.2))).mass (b, x) =
      p.mass b * r.mass x := by
  classical
  simp only [FiniteLaw.map_mass, FiniteLaw.joint, Fintype.sum_prod_type,
    Prod.mk.injEq]
  calc
    (∑ b', ∑ a, if b' = b ∧ f a = x then p.mass b' * (q b').mass a else 0) =
        ∑ a, if f a = x then p.mass b * (q b).mass a else 0 := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro b' _ hne
        simp [hne]
      · simp
    _ = p.mass b * ((q b).map f).mass x := by
      rw [FiniteLaw.map_mass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    _ = _ := by rw [hq]

theorem common_marginal_entropy (p : FiniteLaw B) (q : B → FiniteLaw A)
    (f : A → X) (r : FiniteLaw X)
    (hq : ∀ b x, ((q b).map f).mass x = r.mass x) :
    (∑ b, p.mass b * finiteEntropy ((q b).map f).mass) =
      finiteEntropy r.mass := by
  have heq (b : B) : ((q b).map f).mass = r.mass := funext (hq b)
  simp_rw [heq]
  rw [← Finset.sum_mul, p.total, one_mul]

theorem independent_entropy (p : FiniteLaw A) (q : FiniteLaw B) :
    finiteEntropy (p.joint (fun _ => q)).mass =
      finiteEntropy p.mass + finiteEntropy q.mass := by
  rw [FiniteLaw.joint_entropy, ← Finset.sum_mul, p.total, one_mul]

end MatrixMultiplication.CompletionLaws

end

end OAI
