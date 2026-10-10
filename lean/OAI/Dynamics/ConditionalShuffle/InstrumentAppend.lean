import OAI.Dynamics.ConditionalShuffle.InstrumentBound

namespace OAI

noncomputable section
namespace Revealed.Instrument
open scoped Classical
open Thorp Thorp.Fourier
variable {E S G Ω : Type} [fintype_S : Fintype S] [fintype_G : Fintype G] [group_G : Group G] [fintype_Ω : Fintype Ω] [nonempty_Ω : Nonempty Ω]
variable (I : Data E S G Ω)

lemma base_snoc (e : E) (n : ℕ) (p : Fin n → S) (s : S) :
    base I e (n+1) (Fin.snoc p s) = I.next (base I e n p) s := by
  let retained_fintype_S := fintype_S
  let retained_fintype_G := fintype_G
  let retained_group_G := group_G
  let retained_fintype_Ω := fintype_Ω
  let retained_nonempty_Ω := nonempty_Ω
  simp only [base, Fin.init_snoc, Fin.snoc_last]

lemma weights_snoc (e : E) (n : ℕ) (p : Fin n → S) (s : S) :
    weights I e (n+1) (Fin.snoc p s) = weights I e n p * probability I (base I e n p) s := by
  let retained_fintype_S := fintype_S
  let retained_group_G := group_G
  let retained_nonempty_Ω := nonempty_Ω
  simp only [weights, Fin.init_snoc, Fin.snoc_last]

lemma kernels_snoc (e : E) (n : ℕ) (p : Fin n → S) (s : S) :
    kernels I e (n+1) (Fin.snoc p s) = Fin.snoc (kernels I e n p) (kernel I (base I e n p) s) := by
  let retained_fintype_S := fintype_S
  let retained_group_G := group_G
  let retained_nonempty_Ω := nonempty_Ω
  simp only [kernels, Fin.init_snoc, Fin.snoc_last]

lemma base_append (e : E) (n m : ℕ) (p : Fin n → S) (q : Fin m → S) :
    base I e (n+m) (Fin.append p q) = base I (base I e n p) m q := by
  induction m with
  | zero =>
      have hz : Fin.append p q = p := by funext i; exact Fin.append_left p q i
      rw [hz]
      rfl
  | succ m ih =>
      obtain ⟨⟨s,q⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (m+1) => S)).surjective q
      erw [Fin.append_snoc, base_snoc, base_snoc, ih]

lemma weights_append (e : E) (n m : ℕ) (p : Fin n → S) (q : Fin m → S) :
    weights I e (n+m) (Fin.append p q) = weights I e n p * weights I (base I e n p) m q := by
  induction m with
  | zero =>
      have hz : Fin.append p q = p := by funext i; exact Fin.append_left p q i
      rw [hz, weights, mul_one]
      rfl
  | succ m ih =>
      obtain ⟨⟨s,q⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (m+1) => S)).surjective q
      erw [Fin.append_snoc, weights_snoc, weights_snoc, ih, base_append, mul_assoc]

lemma kernels_append (e : E) (n m : ℕ) (p : Fin n → S) (q : Fin m → S) :
    kernels I e (n+m) (Fin.append p q) =
      Fin.append (kernels I e n p) (kernels I (base I e n p) m q) := by
  induction m with
  | zero =>
      have hp : Fin.append p q = p := by funext i; exact Fin.append_left p q i
      rw [hp]
      funext i
      exact (Fin.append_left _ _ i).symm
  | succ m ih =>
      obtain ⟨⟨s,q⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (m+1) => S)).surjective q
      erw [Fin.append_snoc, kernels_snoc, kernels_snoc, ih, base_append, Fin.append_snoc]

lemma realConv_assoc (μ ν η : G → ℝ) : realConv (realConv μ ν) η = realConv μ (realConv ν η) := by
  funext z
  simp only [realConv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have h := Equiv.sum_comp (Equiv.mulLeft a) (fun b => μ a * ν (a⁻¹*b) * η (b⁻¹*z))
  change (∑ b, μ a * ν (a⁻¹*(a*b)) * η ((a*b)⁻¹*z)) = _ at h
  simpa only [inv_mul_cancel_left, mul_inv_rev, mul_assoc] using h.symm

lemma realConv_dirac_one (μ : G → ℝ) : realConv (fun g => if g = 1 then 1 else 0) μ = μ := by
  funext g
  simp [realConv]

lemma realProduct_snoc (n : ℕ) (μ : Fin n → G → ℝ) (ν : G → ℝ) :
    realProduct (n+1) (Fin.snoc μ ν) = realConv ν (realProduct n μ) := by
  simp only [realProduct, Fin.init_snoc, Fin.snoc_last]

lemma realProduct_append (n m : ℕ) (μ : Fin n → G → ℝ) (ν : Fin m → G → ℝ) :
    realProduct (n+m) (Fin.append μ ν) = realConv (realProduct m ν) (realProduct n μ) := by
  induction m with
  | zero =>
      have hz : Fin.append μ ν = μ := by funext i; exact Fin.append_left μ ν i
      rw [hz, realProduct, realConv_dirac_one]
      rfl
  | succ m ih =>
      obtain ⟨⟨η,ν⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (m+1) => G → ℝ)).surjective ν
      erw [Fin.append_snoc, realProduct_snoc, realProduct_snoc, ih, realConv_assoc]

end Revealed.Instrument

end

end OAI
