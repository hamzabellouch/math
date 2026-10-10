import OAI.NumberTheory.DirichletL.Detector.GramShell
import OAI.NumberTheory.DirichletL.Detector.GramAnnularCount

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def shellLatticeColumns (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) : Finset O :=
  (elementWindow_finite_support W hW N hN).toFinset

lemma shellLatticeColumns_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N) (n : O) :
    n∈shellLatticeColumns W hW N hN ↔ W (‖eisEmbedding n‖^2/N)≠0 := by
  simp only [shellLatticeColumns,Set.Finite.mem_toFinset,Function.mem_support]
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rfl

lemma shellLatticeColumns_nonzero (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (ha : 0<a) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : n≠0 := by
  intro hz
  have hh := (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).1
  simp only [hz,map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div] at hh
  linarith

lemma shellLatticeColumns_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (a b : ℝ) (hs : Function.support W⊆Set.Icc a b) (n : O)
    (hn : n∈shellLatticeColumns W hW N hN) : ‖eisEmbedding n‖^2≤b*N :=
  (div_le_iff₀ hN).mp (hs ((shellLatticeColumns_mem W hW N hN n).mp hn)).2

lemma shell_lattice_support (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (n m : O)
    (h : n∉shellLatticeColumns W hW N hN ∨ m∉shellLatticeColumns W hW N hN) :
    shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N)=0 := by
  rcases h with h|h
  · apply shellProfile_zero_left
    simpa only [shellLatticeColumns_mem,not_not] using h
  · apply shellProfile_zero_right
    simpa only [shellLatticeColumns_mem,not_not] using h

lemma shell_lattice_summable (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    Summable (fun m : O×O=>f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N)) := by
  apply summable_of_ne_finset_zero (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN))
  intro m hm
  have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
  rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero]

lemma shell_lattice_tsum (W : ℝ→ℂ) (hW : HasCompactSupport W) (N : ℝ) (hN : 0<N)
    (U : SchwartzMap ℝ ℂ) (v T : ℝ) (f : O→O→ℂ) :
    (∑'m : O×O,f m.1 m.2*shellProfile W v U T (‖eisEmbedding m.1‖^2/N) (‖eisEmbedding m.2‖^2/N))=
      ∑n∈shellLatticeColumns W hW N hN,∑m∈shellLatticeColumns W hW N hN,
        f n m*shellProfile W v U T (‖eisEmbedding n‖^2/N) (‖eisEmbedding m‖^2/N) := by
  rw [tsum_eq_sum (s:=(shellLatticeColumns W hW N hN)×ˢ(shellLatticeColumns W hW N hN)) (by
    intro m hm
    have h : m.1∉shellLatticeColumns W hW N hN ∨ m.2∉shellLatticeColumns W hW N hN := by simpa only [Finset.mem_product,not_and_or] using hm
    rw [shell_lattice_support W hW N hN U v T m.1 m.2 h,mul_zero])]
  exact Finset.sum_product _ _ _

end SevenEighths.ProbeGramCommon
end

end OAI
