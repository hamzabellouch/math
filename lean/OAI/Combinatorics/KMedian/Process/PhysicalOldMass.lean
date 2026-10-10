import Mathlib
import OAI.Combinatorics.KMedian.Preparation.CoupledGeometry
import OAI.Combinatorics.KMedian.Preparation.CoupledNoise

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

noncomputable def oldAssignment {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) : Physical I T → ℝ :=
  Sum.elim (fun i => if i ∈ F ∩ outside P then L.N z.1 (.inl i) else 0)
    (fun ti => if ti.2 ∈ F then g*(L.C z.1 z.2 ti:ℝ) else 0)

 theorem old_feasible {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hg : 0 ≤ g) (F : Finset I) (z : L.Ω × (T → Finset I))
    (hz : 0 < (L.ν.joint L.κ).weight z) :
    ∀ a, 0 ≤ oldAssignment L F z a ∧ oldAssignment L F z a ≤ physicalOpen L z a := by
  have hω := (L.ν.support_joint L.κ z hz).1
  rintro (i | ti)
  · dsimp only [oldAssignment,physicalOpen,physicalCount,Sum.elim_inl]
    split_ifs
    · exact ⟨L.nominal_nonneg z.1 hω _,L.nominal_cap z.1 hω _⟩
    · exact ⟨le_rfl,mul_nonneg hg (Nat.cast_nonneg _)⟩
  · dsimp only [oldAssignment,physicalOpen,physicalCount,Sum.elim_inr]
    split_ifs
    · exact ⟨mul_nonneg hg (Nat.cast_nonneg _),le_rfl⟩
    · exact ⟨le_rfl,mul_nonneg hg (Nat.cast_nonneg _)⟩

 theorem old_mass_id {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) :
    (∑ a, oldAssignment L F z a)=
      (∑ i ∈ F ∩ outside P, (if i ∈ outside P then L.N z.1 (.inl i) else y i))+
      (∑ t, ∑ i ∈ F, g*(L.C z.1 z.2 (t,i):ℝ)) := by
  simp only [oldAssignment,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr,sum_ite_mem,univ_inter]
  congr 1
  apply sum_congr rfl
  intro i hi
  exact (ite_eq_left (mem_inter.mp hi).2).symm

 theorem old_cost_id {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ} {g γ B : ℝ} {Δ : ℕ}
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (F : Finset I) (z : L.Ω × (T → Finset I)) (d : I → ℝ) :
    (∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a))=
      (∑ i ∈ F ∩ outside P, (if i ∈ outside P then L.N z.1 (.inl i) else y i)*d i)+
      (∑ t, ∑ i ∈ F, (g*(L.C z.1 z.2 (t,i):ℝ))*d i) := by
  simp only [oldAssignment,Fintype.sum_sum_type,Fintype.sum_prod_type,
    Sum.elim_inl,Sum.elim_inr,ite_mul,zero_mul,sum_ite_mem,univ_inter]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [ite_eq_left (mem_inter.mp hi).2]

theorem physical_old_estimates {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ}
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (L.ν.joint L.κ).expect (fun z => max (1-∑ a, oldAssignment L F z a) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    (L.ν.joint L.κ).expect (fun z => ∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ F, y i*d i)/p₀ := by
  have he := coupled_old_estimates P A y p c hg hγ hunit L hy hp₀ hp₀1 hp hc0 hc1 hP F hF d hd
  dsimp only at he
  simpa only [old_mass_id,old_cost_id,sub_add_eq_sub_sub] using he

end MetricKMedian.Preparation
end
end

end OAI
