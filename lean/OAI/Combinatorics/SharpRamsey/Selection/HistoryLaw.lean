import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.NullFreeLaw

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]

def Law.sigma (μ : Law Θ) {A : Θ→Type*} [∀ z,Fintype (A z)]
    (ρ : ∀ z,Law (A z)) : Law (Sigma A) where
  mass x := μ.mass x.1*(ρ x.1).mass x.2
  nonneg x := mul_nonneg (μ.nonneg x.1) ((ρ x.1).nonneg x.2)
  total := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ z,μ.mass z := by
        apply sum_congr rfl
        intro z _
        change (∑ y,μ.mass z*(ρ z).mass y)=μ.mass z
        rw [←mul_sum,(ρ z).total,mul_one]
      _ = 1 := μ.total

lemma Law.sigma_sum (μ : Law Θ) {A : Θ→Type*} [∀ z,Fintype (A z)]
    (ρ : ∀ z,Law (A z)) (f : Sigma A→ℝ) :
    (∑ x,(μ.sigma ρ).mass x*f x)=∑ z,μ.mass z*∑ a,(ρ z).mass a*f ⟨z,a⟩ := by
  simp only [Law.sigma,Fintype.sum_sigma,mul_sum,mul_assoc]

lemma Law.history_sum (μ : Law Ω) (θ : Ω→Θ) (f : Ω→ℝ) :
    (∑ z,(μ.map θ).mass z*∑ ω,(μ.cond θ z).mass ω*f ω)=∑ ω,μ.mass ω*f ω := by
  have h:=μ.history_observable_sum θ id (fun _ ω=>f ω)
  simpa only [Law.sum_map,id_eq] using h.symm

lemma Law.nullFree_map {B : Type*} [Fintype B] (μ : Law Ω) (f : Ω→B) :
    μ.nullFree.map (fun ω=>f ω.val)=μ.map f := by
  ext b
  change (∑ ω : {ω // μ.mass ω≠0} with f ω.val=b,μ.mass ω.val)=∑ ω with f ω=b,μ.mass ω
  simpa only [sum_filter,mul_ite,mul_one,mul_zero,Law.nullFree] using
    μ.nullFree_integral (fun ω=>if f ω=b then 1 else 0)

abbrev Law.History (μ : Law Ω) (θ : Ω→Θ) := {z // (μ.map θ).mass z≠0}

abbrev Law.HistorySource (μ : Law Ω) (θ : Ω→Θ) (z : μ.History θ) :=
  {ω // (μ.cond θ z.val).mass ω≠0}

abbrev Law.HistoryExtension (μ : Law Ω) (θ : Ω→Θ)
    (A : μ.History θ→Type*) := Σ z : μ.History θ, μ.HistorySource θ z × A z

def Law.historyExtension (μ : Law Ω) (θ : Ω→Θ)
    {A : μ.History θ→Type*} [∀ z,Fintype (A z)]
    (ρ : ∀ z,Law (A z)) : Law (μ.HistoryExtension θ A) :=
  (μ.map θ).nullFree.sigma (fun z=>(μ.cond θ z.val).nullFree.prod (ρ z))

lemma Law.historyExtension_support (μ : Law Ω) (θ : Ω→Θ)
    {A : μ.History θ→Type*} (x : μ.HistoryExtension θ A) :
    μ.mass x.2.1.val≠0 ∧ θ x.2.1.val=x.1.val :=
  μ.cond_support θ x.1.val x.1.property x.2.1.val x.2.1.property

theorem Law.historyExtension_source (μ : Law Ω) (θ : Ω→Θ)
    {A : μ.History θ→Type*} [∀ z,Fintype (A z)]
    (ρ : ∀ z,Law (A z)) (f : Ω→ℝ) :
    (∑ x,(μ.historyExtension θ ρ).mass x*f x.2.1.val)=∑ ω,μ.mass ω*f ω := by
  unfold Law.historyExtension
  rw [Law.sigma_sum]
  change (∑ z,(μ.map θ).nullFree.mass z *
    ∑ x,((μ.cond θ z.val).nullFree.prod (ρ z)).mass x*f x.1.val)=_
  have he (z : μ.History θ) :
      (∑ x,((μ.cond θ z.val).nullFree.prod (ρ z)).mass x*f x.1.val)=
      ∑ ω,(μ.cond θ z.val).mass ω*f ω := by
    rw [Law.prod_left_sum (μ.cond θ z.val).nullFree (ρ z) (fun ω=>f ω.val)]
    exact (μ.cond θ z.val).nullFree_integral f
  simp_rw [he]
  exact ((μ.map θ).nullFree_integral (fun z=>∑ ω,(μ.cond θ z).mass ω*f ω)).trans
    (μ.history_sum θ f)

theorem Law.historyExtension_bound (μ : Law Ω) (θ : Ω→Θ)
    {A : μ.History θ→Type*} [∀ z,Fintype (A z)]
    (ρ : ∀ z,Law (A z)) (f : μ.HistoryExtension θ A→ℝ) (c : ℝ)
    (h : ∀ z,(∑ x,((μ.cond θ z.val).nullFree.prod (ρ z)).mass x*f ⟨z,x⟩)≤c) :
    (∑ x,(μ.historyExtension θ ρ).mass x*f x)≤c := by
  unfold Law.historyExtension
  rw [Law.sigma_sum]
  calc
    _ ≤ ∑ z,(μ.map θ).nullFree.mass z*c :=
      sum_le_sum (fun z _=>mul_le_mul_of_nonneg_left (h z) ((μ.map θ).nullFree.nonneg z))
    _ = c := by rw [←sum_mul,Law.total,one_mul]

end
end SharpLogRamsey.Selection

end

end OAI
