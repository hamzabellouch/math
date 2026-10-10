import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def finitePolicyPMF {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) : ℕ → PMF (List G)
  | 0 => PMF.pure []
  | n+1 => (Q i ω x).bind fun u => (finitePolicyPMF Q ω (i+1) (x+u) n).map (List.cons u)

lemma pmf_map_cons {G : Type*} (p : PMF (List G)) (u v : G) (w : List G) :
    (p.map (List.cons u)) (v::w) = if v=u then p w else 0 := by
  rw [PMF.map_apply]
  by_cases huv : v=u
  · subst v
    simp only [List.cons.injEq,true_and]
    simp only [ite_true,eq_comm (a := w)]
    exact tsum_ite_eq w fun a => p a
  · simp [huv]

lemma finitePolicyPMF_cons {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x u : G) (n : ℕ) (w : List G) :
    finitePolicyPMF Q ω i x (n+1) (u::w) =
      Q i ω x u * finitePolicyPMF Q ω (i+1) (x+u) n w := by
  simp only [finitePolicyPMF,PMF.bind_apply,pmf_map_cons,mul_ite,mul_zero]
  simpa only [eq_comm (a := u)] using
    (tsum_ite_eq u fun a => Q i ω x a * finitePolicyPMF Q ω (i+1) (x+a) n w)

lemma finitePolicyPMF_nil_succ {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ) :
    finitePolicyPMF Q ω i x (n+1) [] = 0 := by
  simp [finitePolicyPMF,PMF.bind_apply,PMF.map_apply]

lemma finitePolicyPMF_length {Ω G : Type*} [Add G]
    (Q : ℕ → Ω → G → PMF G) (ω : Ω) (i : ℕ) (x : G) (n : ℕ) (w : List G)
    (hw : w.length ≠ n) : finitePolicyPMF Q ω i x n w = 0 := by
  induction n generalizing i x w with
  | zero =>
    have he : w ≠ [] := by intro h; subst w; exact hw rfl
    simp [finitePolicyPMF,PMF.pure_apply,he]
  | succ n ih =>
    cases w with
    | nil => exact finitePolicyPMF_nil_succ Q ω i x n
    | cons u w =>
      rw [finitePolicyPMF_cons,ih]
      · simp
      · simpa using hw

lemma finitePolicyPMF_measurable_atom {Ω G : Type*} [MeasurableSpace Ω] [Add G]
    (Q : ℕ → Ω → G → PMF G) (hQ : ∀ i x u, Measurable (fun ω => Q i ω x u))
    (i : ℕ) (x : G) (n : ℕ) (w : List G) :
    Measurable (fun ω => finitePolicyPMF Q ω i x n w) := by
  induction n generalizing i x w with
  | zero => exact measurable_const
  | succ n ih =>
    cases w with
    | nil => simpa only [finitePolicyPMF_nil_succ] using (measurable_const (a := (0:ℝ≥0∞)))
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      exact (hQ i x u).mul (ih (i+1) (x+u) w)

end DirectionalTransience

end

end

end OAI
