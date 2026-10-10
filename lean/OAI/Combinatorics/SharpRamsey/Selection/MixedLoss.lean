import Mathlib
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedReplacement
import OAI.Combinatorics.SharpRamsey.Exposure.MixtureRealization

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {X Ω B A Θ : Type*} [Fintype X] [Fintype Ω] [Fintype B] [Fintype A] [Fintype Θ]

lemma Law.attach_left (q : Law X) (μ : Law Ω) (f : X→B) (g : Ω→B) (φ : X→ℝ) :
    (∑ x,(q.attach μ f g).mass x*φ x.1)=∑ x,q.mass x*φ x := by
  rw [Law.attach,Law.sigma_sum]
  apply sum_congr rfl
  intro x _
  change q.mass x*(∑ a,(μ.cond g (f x)).mass a*φ x)=q.mass x*φ x
  rw [←sum_mul,(μ.cond g (f x)).total,one_mul]

theorem Law.mixed_loss (ν : Law Θ) {Y : {θ // ν.mass θ≠0}→Type*}
    [∀ θ,Fintype (Y θ)] (μ : ∀ θ,Law (Y θ)) (p : Law A)
    (N : ℕ) (pop : Θ→ℕ) (out : A→(Σ θ,Y θ)→ℕ) (δ : ℝ) (hδ : 0≤δ)
    (hsize : ∀ θ,pop θ≤N)
    (hlocal : ∀ θ,(∑ a,p.mass a*∑ y,(μ θ).mass y*((pop θ.val:ℝ)-(out a ⟨θ,y⟩:ℝ)))≤
      (pop θ.val:ℝ)*δ) :
    (∑ a,p.mass a*∑ ω,(ν.nullFree.sigma μ).mass ω*((N:ℝ)-(out a ω:ℝ)))≤
      (∑ θ,ν.mass θ*((N:ℝ)-(pop θ:ℝ)))+(N:ℝ)*δ := by
  have hloc (θ : {θ // ν.mass θ≠0}) :
      (∑ a,p.mass a*∑ y,(μ θ).mass y*((N:ℝ)-(out a ⟨θ,y⟩:ℝ)))≤
        (N:ℝ)-(pop θ.val:ℝ)+(N:ℝ)*δ := by
    calc
      _ = (N:ℝ)-(pop θ.val:ℝ)+
          ∑ a,p.mass a*∑ y,(μ θ).mass y*((pop θ.val:ℝ)-(out a ⟨θ,y⟩:ℝ)) := by
        have he (a : A) (y : Y θ) : (N:ℝ)-(out a ⟨θ,y⟩:ℝ)=
            ((N:ℝ)-(pop θ.val:ℝ))+((pop θ.val:ℝ)-(out a ⟨θ,y⟩:ℝ)) := by ring
        simp_rw [he]
        simp only [mul_add,sum_add_distrib,←sum_mul,(μ θ).total,p.total,one_mul]
      _ ≤ _ := add_le_add le_rfl ((hlocal θ).trans
        (mul_le_mul_of_nonneg_right (show (pop θ.val:ℝ)≤(N:ℝ) by exact_mod_cast hsize θ.val) hδ))
  calc
    _ = ∑ θ,ν.nullFree.mass θ*(∑ a,p.mass a*
        ∑ y,(μ θ).mass y*((N:ℝ)-(out a ⟨θ,y⟩:ℝ))) := by
      simp_rw [Law.sigma_sum,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro θ _
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro y _
      ring
    _ ≤ ∑ θ,ν.nullFree.mass θ*((N:ℝ)-(pop θ.val:ℝ)+(N:ℝ)*δ) :=
      sum_le_sum (fun θ _=>mul_le_mul_of_nonneg_left (hloc θ) (ν.nullFree.nonneg θ))
    _ = _ := by
      rw [ν.nullFree_integral (fun θ=>(N:ℝ)-(pop θ:ℝ)+(N:ℝ)*δ)]
      simp only [mul_add,sum_add_distrib,←sum_mul,ν.total,one_mul]

end
end SharpLogRamsey.Selection

end

end OAI
