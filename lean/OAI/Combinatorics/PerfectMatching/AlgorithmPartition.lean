import OAI.Combinatorics.PerfectMatching.Partition
import OAI.Combinatorics.PerfectMatching.Ascent

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset MatchingEntropy

def smoothObjective (G : Input) (x : Pair G.n → ℝ) : ℝ :=
  entropy x/Real.log 2+∑ e,(beta G e:ℝ)*x e

def Z (G : Input) : ℝ := (completeGraph G.n).weightedZ (fun e => (beta G e:ℝ))
def logZ (G : Input) : ℝ := Real.log (Z G)/Real.log 2

lemma complete_matching_nonempty {n : ℕ} (hn : 4≤ n) (heven : Even n) :
    Nonempty (completeGraph n).Matching := by
  obtain ⟨p,hp⟩ := ((completeGraph n).mem_polytope_iff _).mp (uniform_feasible hn heven)
  by_contra h
  have : IsEmpty (completeGraph n).Matching := not_nonempty_iff.mp h
  simpa using hp.1.2

lemma mass_half {n : ℕ} (heven : Even n) {x : Pair n → ℝ}
    (hx : x∈(completeGraph n).polytope) : (∑ e,x e)=(n:ℝ)/2 := by
  obtain ⟨r,hr⟩ := heven
  have hn : Fintype.card (Fin n)=2*r := by simp; omega
  rw [(completeGraph n).marginal_sum hn hx]
  have hn' : (n:ℝ)=2*(r:ℝ) := by exact_mod_cast (show n=2*r by omega)
  rw [hn']; ring

lemma q_dyadic_le_one (n : ℕ) : (q n:ℝ)*dyadic (K n)≤1 := by
  have hh : (q n:ℝ)≤(2:ℝ)^(K n) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1<2) (q n)
  rw [dyadic,inv_pow,←div_eq_mul_inv]
  exact (div_le_one (by positivity)).mpr hh

lemma objective_compare (G : Input) (hn : 2≤ G.n) (heven : Even G.n)
    {x : Pair G.n → ℝ} (hx : x∈(completeGraph G.n).polytope) :
    objective G x≤ smoothObjective G x ∧ smoothObjective G x≤ objective G x+G.n := by
  have he : smoothObjective G x-objective G x=
      ∑ e,(phi (x e)-psiReal (K G.n) (x e)) := by
    simp only [smoothObjective,objective,phi,entropy,sum_add_distrib,sum_sub_distrib,←sum_div]
    ring
  have hnon : 0≤∑ e,(phi (x e)-psiReal (K G.n) (x e)) :=
    sum_nonneg fun e _ => (dyadic_entropy_error (K G.n) ((completeGraph G.n).coordinate_mem_Icc hx e)).1
  have hupper : (∑ e,(phi (x e)-psiReal (K G.n) (x e)))≤(G.n:ℝ)/2+1 := by
    calc
      _ ≤ ∑ e,(x e+dyadic (K G.n)) := sum_le_sum fun e _ =>
        (dyadic_entropy_error (K G.n) ((completeGraph G.n).coordinate_mem_Icc hx e)).2
      _ = (G.n:ℝ)/2+(q G.n:ℝ)*dyadic (K G.n) := by
        rw [sum_add_distrib,mass_half heven hx]; simp [q]
      _ ≤ _ := by linarith [q_dyadic_le_one G.n]
  have hn' : (2:ℝ)≤ G.n := by exact_mod_cast hn
  constructor <;> linarith

lemma Z_pos (G : Input) (hn : 4≤ G.n) (heven : Even G.n) : 0< Z G := by
  have := complete_matching_nonempty hn heven
  exact expSum_pos _

lemma smooth_lower_partition (G : Input) (hn : 4≤ G.n) (heven : Even G.n)
    {x : Pair G.n → ℝ} (hx : x∈(completeGraph G.n).polytope) :
    smoothObjective G x-4*(G.n:ℝ)≤ logZ G := by
  have hPM := complete_matching_nonempty hn heven
  obtain ⟨r,hr⟩ := heven
  have hn' : Fintype.card (Fin G.n)=2*r := by simp; omega
  have hent := ((completeGraph G.n).entropy_binary_scale hPM hn' hx).1
  have hvar := (completeGraph G.n).weighted_variational_le (fun e => (beta G e:ℝ)) hx
  simp only [Fintype.card_fin] at hent
  dsimp only [smoothObjective,logZ,Z]
  linarith

lemma smooth_upper_partition (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    ∃ x∈(completeGraph G.n).polytope,logZ G≤ smoothObjective G x+G.n := by
  have hPM := complete_matching_nonempty hn heven
  obtain ⟨x,hx,hvar⟩ := (completeGraph G.n).weighted_variational_attained (fun e => (beta G e:ℝ))
  obtain ⟨r,hr⟩ := heven
  have hn' : Fintype.card (Fin G.n)=2*r := by simp; omega
  have hent := ((completeGraph G.n).entropy_binary_scale hPM hn' hx).2
  simp only [Fintype.card_fin] at hent
  refine ⟨x,hx,?_⟩
  dsimp only [smoothObjective,logZ,Z]
  linarith

theorem R_partition_bracket (G : Input) (hn : 4≤ G.n) (heven : Even G.n) :
    (R G:ℝ)-4*(G.n:ℝ)≤ logZ G ∧ logZ G≤(R G:ℝ)+3*(G.n:ℝ) := by
  obtain ⟨⟨y,hy,hylow⟩,hupp⟩ := R_objective_bracket G hn heven
  constructor
  · have hobj := (objective_compare G (by omega) heven hy).1
    have hpart := smooth_lower_partition G hn heven hy
    linarith
  · obtain ⟨x,hx,hpart⟩ := smooth_upper_partition G hn heven
    have hobj := (objective_compare G (by omega) heven hx).2
    have hU := hupp x hx
    have hn' : (4:ℝ)≤ G.n := by exact_mod_cast hn
    linarith

end
end BinaryMatching.Algorithm
end

end OAI
