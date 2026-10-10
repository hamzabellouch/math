import OAI.Geometry.TranslativeCovering.PatternTail

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace SourceLocalization
open Set Metric MeasureTheory SourceParameters LocalizationRates LocalizationRounding PatternGeometry PatternEnumeration
open scoped ENNReal Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Patterns (n : ℕ) (R : ℝ) := Retained n (N n R) (h n) (L n) a D (rround n) (RadialShell.high a n) (2*Cloc*R)
lemma good_mono_inner {n : ℕ} {J : Type u_1} [Fintype J] (p : J → Space n)
    {a D r r' b C : ℝ} (hr : r'≤r) : roundedGood p a D r b C ⊆ roundedGood p a D r' b C := by
  intro y hy
  exact ⟨hy.1,fun i => hr.trans (hy.2.1 i),hy.2.2⟩
lemma low_le {n : ℕ} : RadialShell.low a n ≤ rround n := by
  have he : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
  dsimp [RadialShell.low,rround,rminus]
  simp only [mul_div_assoc]
  linarith only [he]
lemma pattern_good {n : ℕ} {R : ℝ} (P : Patterns n R) :
    volume (closedBall (0:Space n) D) ≤ 4*volume (roundedGood (points P.val) a D
      (RadialShell.low a n) (RadialShell.high a n) (2*Cloc*R)) :=
  P.property.trans (mul_le_mul_right (measure_mono (good_mono_inner _ low_le)) 4)
lemma localize {n : ℕ} [NeZero n] {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2) (hn : 1≤n)
    (hr : 0<rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
    (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1)
    (hρ : ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a) ≤ ENNReal.ofReal (R/(2*v)))
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hc : ∀ y,∃ (i:I) (l:Λ), y-p i-l.val ∈ RandomBody.body (b n) 1 U) :
    ∃ P : Patterns n R,U ∈ PatternTail.coverEvent (points P.val) a D := by
  have hm := LocalizationMeans.bounds Λ p hF hF0 hFtop hR hRn hr hβ houter hinner hρ
  have he := EntropyRates.error_bound hn
  have he0 : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
  have hh := EntropyRates.mesh_pos (by omega : 0<n)
  have hC : 0≤Cloc*R := by
    have hCl : 0<Cloc := by norm_num [Cloc,v]
    exact mul_nonneg hCl.le (by linarith only [hR])
  have hN : 0<N n R := by
    apply Nat.ceil_pos.mpr
    have hL : 0<L n := by
      have ha := a_pos; have hD := D_pos
      dsimp [L,b]; positivity
    have hv : 0<v := by norm_num [v]
    have ha := a_pos
    positivity
  obtain ⟨S,q,hS,hq,hg,hcover⟩ := LocalizationComplete.localize Λ p hF hF0 hFtop a_pos D_pos hh hC
    (show D+b n≤W n by dsimp [W]; linarith only [he0])
    (show RadialShell.high a n+Real.sqrt n*h n/2≤β n by dsimp [RadialShell.high,β,b]; linarith only [he]) hlip hN hm.1 hm.2 U hc
  have hq' (j:S) : q j ∈ alphabet n (h n) (L n) := by
    obtain ⟨hz,hbound⟩ := (mem_alphabet hh _).mp (hq j)
    apply (mem_alphabet hh _).mpr ⟨hz,?_⟩
    apply hbound.trans
    dsimp [W,L]
    linarith only [he]
  have hg' : volume (closedBall (0:Space n) D) ≤ 4*volume (roundedGood q a D (rround n) (RadialShell.high a n) (2*Cloc*R)) := by
    have sub := good_mono_inner q (show rround n≤rminus n-Real.sqrt n*h n/2 by dsimp [rround]; linarith only [he,he0]) (a:=a) (D:=D) (b:=RadialShell.high a n) (C:=2*(Cloc*R))
    have hh := hg.trans (mul_le_mul_right (measure_mono sub) 2)
    have heq : 2*(Cloc*R)=2*Cloc*R := by ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_left (by norm_num : (2:ℝ≥0∞)≤4) _)
  obtain ⟨P,e,hp⟩ := encode_retained q (by simpa using hS) hq' hg'
  refine ⟨P,?_⟩
  intro y hy
  obtain ⟨j,hj⟩ := hcover y hy
  obtain ⟨i,rfl⟩ := e.surjective j
  rw [hp]
  refine ⟨i,?_,?_⟩
  · apply closedBall_subset_closedBall (show b n+Real.sqrt n*h n/2≤RadialShell.high a n by dsimp [RadialShell.high,b]; linarith only [he,he0]) hj.1
  · simp only [RandomBody.body,Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq] at hj ⊢
    intro u
    exact (hj.2 u).trans (by linarith only [he,he0])
end SourceLocalization

end OAI
