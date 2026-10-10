import OAI.Analysis.AllenCahn.JetProducts
import OAI.Analysis.AllenCahn.JetCompactness

namespace OAI

noncomputable section
namespace DeGiorgiCompactness
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff

lemma coherentJets_eq_of_base {n : ℕ} {g h : JetSpace n}
    (hg : CoherentJets g) (hh : CoherentJets h) (he : g [] = h []) : g = h := by
  funext l
  induction l with
  | nil => exact he
  | cons i l ih =>
    ext x
    rw [← (hg l).2 i x, ← (hh l).2 i x, ih]

lemma coherentJets_add_smul {n : ℕ} {g h : JetSpace n}
    (hg : CoherentJets g) (hh : CoherentJets h) (a b : ℝ) :
    CoherentJets (a • g + b • h) := by
  intro l
  have hs : Differentiable ℝ (fun x => a*g l x+b*h l x) :=
    ((hg l).1.const_mul a).add ((hh l).1.const_mul b)
  refine ⟨hs, ?_⟩
  intro i x
  change coordDeriv (fun y => a*g l y+b*h l y) i x = a*g (i::l) x+b*h (i::l) x
  unfold coordDeriv
  rw [fderiv_fun_add (((hg l).1 x).const_mul a) (((hh l).1 x).const_mul b),
    fderiv_const_mul ((hg l).1 x), fderiv_const_mul ((hh l).1 x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  change a*coordDeriv (g l) i x+b*coordDeriv (h l) i x = _
  rw [(hg l).2, (hh l).2]

def pdeJetCone {n : ℕ} (P : Space n → ℝ) : Set (JetSpace n) :=
  {g | CoherentJets g ∧ (∀ x, 0 ≤ g [] x) ∧
    (∀ x, (∑ i : Fin n, g [i,i] x) = P x*g [] x) ∧ g [] 0 = 1}

lemma pdeJetCone_closed {n : ℕ} (P : Space n → ℝ) : IsClosed (pdeJetCone P) := by
  have he (l : List (Fin n)) (x : Space n) : Continuous (fun g : JetSpace n => g l x) :=
    (continuous_eval_const x).comp (continuous_apply l)
  have heq : pdeJetCone P = {g : JetSpace n | CoherentJets g} ∩
      ((⋂ x, {g : JetSpace n | 0 ≤ g [] x}) ∩
        ((⋂ x, {g : JetSpace n | (∑ i : Fin n, g [i,i] x) = P x*g [] x}) ∩
          {g : JetSpace n | g [] 0=1})) := by
    ext g
    simp only [pdeJetCone, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact (coherentJets_closed n).inter ((isClosed_iInter (fun x =>
    isClosed_le continuous_const (he [] x))).inter ((isClosed_iInter (fun x =>
      isClosed_eq (continuous_finsetSum _ (fun i _ => he [i,i] x))
        (continuous_const.mul (he [] x)))).inter (isClosed_eq (he [] 0) continuous_const)))

lemma pdeJetCone_convex {n : ℕ} (P : Space n → ℝ) : Convex ℝ (pdeJetCone P) := by
  intro g hg h hh a b ha hb hab
  refine ⟨coherentJets_add_smul hg.1 hh.1 a b, fun x => ?_, fun x => ?_, ?_⟩
  · change 0 ≤ a*g [] x+b*h [] x
    exact add_nonneg (mul_nonneg ha (hg.2.1 x)) (mul_nonneg hb (hh.2.1 x))
  · change (∑ i : Fin n, (a*g [i,i] x+b*h [i,i] x)) = P x*(a*g [] x+b*h [] x)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hg.2.2.1 x, hh.2.2.1 x]
    ring
  · change a*g [] 0+b*h [] 0=1
    rw [hg.2.2.2, hh.2.2.2, mul_one, mul_one]
    exact hab

lemma pdeJetCone_compact_of_local_bounds {n : ℕ} {P : Space n → ℝ}
    (hb : ∀ l R, 0 < R → ∃ M : ℝ≥0, ∀ g ∈ pdeJetCone P, ∀ x, ‖x‖ ≤ R →
      |g l x| ≤ M ∧ ‖fderiv ℝ (g l : Space n → ℝ) x‖ ≤ M) :
    IsCompact (pdeJetCone P) :=
  jetSet_compact_of_local_bounds (pdeJetCone_closed P) (fun _ hg => hg.1) hb

end DeGiorgiCompactness
end

end OAI
