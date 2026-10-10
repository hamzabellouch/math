import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.ExposureReciprocal

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset
open scoped Classical BigOperators NNReal
noncomputable section
universe u v w z
variable {Θ : Type z} {C : Type v} {β : Type w} {ι : Type u}
variable [Fintype Θ] [Fintype C] [Fintype β] [Fintype ι] [DecidableEq ι]

def contextAverage (μ : Law Θ) (f : Θ → ℝ) : ℝ := ∑ θ, μ.mass θ*f θ

lemma contextAverage_mono (μ : Law Θ) {f g : Θ→ℝ}
    (h : ∀ θ,μ.mass θ≠0 → f θ≤g θ) : contextAverage μ f≤contextAverage μ g := by
  apply sum_le_sum
  intro θ _
  by_cases hθ : μ.mass θ=0
  · simp only [hθ,zero_mul,le_refl]
  · exact mul_le_mul_of_nonneg_left (h θ hθ) (μ.nonneg θ)

lemma contextAverage_const (μ : Law Θ) (a : ℝ) : contextAverage μ (fun _ => a)=a := by
  unfold contextAverage
  rw [←sum_mul,μ.total,one_mul]

lemma contextAverage_add (μ : Law Θ) (f g : Θ→ℝ) :
    contextAverage μ (fun θ => f θ+g θ)=contextAverage μ f+contextAverage μ g := by
  simp only [contextAverage,mul_add,sum_add_distrib]

lemma contextAverage_div (μ : Law Θ) (f : Θ→ℝ) (a : ℝ) :
    contextAverage μ (fun θ => f θ/a)=contextAverage μ f/a := by
  simp only [contextAverage,←mul_div_assoc,←sum_div]

lemma contextAverage_mul (μ : Law Θ) (f : Θ→ℝ) (a : ℝ) :
    contextAverage μ (fun θ => a*f θ)=a*contextAverage μ f := by
  simp only [contextAverage,mul_left_comm,←mul_sum]

lemma contextScores_sum (n k : ℕ) (hn : 2≤n) (μ : Law Θ)
    (p : Θ→Law (ι→β)) (e : Θ→C×Fin (n+k) ↪ ι) (own : Θ→ι→Option C)
    (hown : ∀ θ b x,own θ (e θ (b,x))=some b) :
    ∑ t : Fin k,contextAverage μ (fun θ => exposureScores n k (p θ) (e θ) (own θ) t) ≤
      2*contextAverage μ (fun θ => totalCorrelation (p θ)) := by
  simp only [contextAverage]
  rw [sum_comm]
  simp only [←mul_sum]
  rw [mul_sum]
  apply sum_le_sum
  intro θ _
  calc
    _ ≤ μ.mass θ*(2*totalCorrelation (p θ)) :=
      mul_le_mul_of_nonneg_left (exposureScores_sum_le n k hn (p θ) (e θ) (own θ) (hown θ)) (μ.nonneg θ)
    _ = _ := by ring

lemma exists_context_round (n k : ℕ) (hn : 2≤n) (hk : 0<k) (μ : Law Θ)
    (p : Θ→Law (ι→β)) (e : Θ→C×Fin (n+k) ↪ ι) (own : Θ→ι→Option C)
    (hown : ∀ θ b x,own θ (e θ (b,x))=some b) :
    ∃ t : Fin k,
      contextAverage μ (fun θ => exposureScores n k (p θ) (e θ) (own θ) t) ≤
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/(k:ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hconst : (∑ _t : Fin k,
      2*contextAverage μ (fun θ => totalCorrelation (p θ))/(k:ℝ)) =
      2*contextAverage μ (fun θ => totalCorrelation (p θ)) := by
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  obtain ⟨t,_,ht⟩ := exists_le_of_sum_le (univ_nonempty : (univ : Finset (Fin k)).Nonempty)
    ((contextScores_sum n k hn μ p e own hown).trans_eq hconst.symm)
  exact ⟨t,ht⟩

variable {A B : Type w} [Fintype A] [Fintype B]
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_context_good_reciprocal (v : B→V) (w : A→Module.Dual K V)
    {ρ : ℝ} (hρ : 0≤ρ) {r s : ℕ} (hsum : Module.finrank K V=r+s)
    (n k : ℕ) (hn : 2≤n) (hk : 0<k) (J D a M : ℝ) (hD : 0<D) (ha : 0<a) (hM : 0≤M)
    (μ : Law Θ) (p : Θ→Law (ι→A×B)) (e : Θ→C×Fin (n+k) ↪ ι)
    (own : Θ→ι→Option C) (hown : ∀ θ b x,own θ (e θ (b,x))=some b)
    (S : Θ→ι→Finset (A×B))
    (hS : ∀ θ,μ.mass θ≠0 → tupleSupported (p θ) (S θ))
    (hJ : ∀ θ i,Real.log (S θ i).card≤J)
    (hf : ∀ θ,μ.mass θ≠0 → tupleFlags (p θ) v w)
    (ho : ∀ θ,μ.mass θ≠0 → rectangleBound (p θ) v w M) :
    ∃ t : Fin k,
      contextAverage μ (fun θ => chargedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t) ≤
        contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/((k:ℝ)*a)+
        2*Fintype.card ι*M/((n:ℝ)*a) ∧
      (n:ℝ)*contextAverage μ (fun θ => chargedSelectedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t) ≤
        contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/((k:ℝ)*a)+
        2*Fintype.card ι*M/((n:ℝ)*a) := by
  obtain ⟨t,ht⟩ := exists_context_round n k hn hk μ p e own hown
  have hbθ (θ : Θ) (hθ : μ.mass θ≠0) :
      chargedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t ≤
        tupleDeficit J (p θ)/D+exposureScores n k (p θ) (e θ) (own θ) t/a+
        2*Fintype.card ι*M/((n:ℝ)*a) := by
    have hb := chargedBad_budget v w hρ hsum n k (by omega) J D a (Fintype.card ι) M hD ha hM
      (p θ) (e θ) (own θ) (S θ) (hS θ hθ) (hJ θ) le_rfl (hf θ hθ) (ho θ hθ) t
    have hd := exposureDeficits_le n k J (p θ) (e θ) (S θ) (hS θ hθ) (hJ θ) t
    exact hb.trans (by gcongr)
  have hb := contextAverage_mono μ hbθ
  simp only [contextAverage_add,contextAverage_div,contextAverage_const] at hb
  have hbound : contextAverage μ (fun θ => chargedBad v w ρ r s n J D a k (p θ) (e θ) (own θ) t) ≤
      contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
        2*contextAverage μ (fun θ => totalCorrelation (p θ))/((k:ℝ)*a)+
        2*Fintype.card ι*M/((n:ℝ)*a) := by
    calc
      _ ≤ _ := hb
      _ ≤ contextAverage μ (fun θ => tupleDeficit J (p θ))/D+
          (2*contextAverage μ (fun θ => totalCorrelation (p θ))/(k:ℝ))/a+_ := by gcongr
      _ = _ := by rw [div_div]
  refine ⟨t,hbound,le_trans ?_ hbound⟩
  rw [←contextAverage_mul]
  apply contextAverage_mono μ
  intro θ _
  exact chargedSelectedBad_le v w ρ r s n k J D a (p θ) (e θ) (own θ) (hown θ) t

end
end SharpLogRamsey.Selection

end

end OAI
