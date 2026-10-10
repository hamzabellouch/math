import OAI.Geometry.TranslativeCovering.PatternWitness

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

namespace CrossDeployment
open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps
open scoped BigOperators

theorem fine {a l u₀ u K : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hK : 0 ≤ K) :
    ∃ H : ℝ,0 < H ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ (e f g : Sphere n) (r s : ℝ),
    RadialShell.low a n ≤ r → r ≤ RadialShell.high a n →
    RadialShell.low a n ≤ s → s ≤ RadialShell.high a n →
    ∀ E F : Set (Sphere n),
    E ⊆ cap f.val ((1+3*RadialShell.η n)/r) →
    F ⊆ cap g.val ((1+3*RadialShell.η n)/s) →
    Real.exp (-K*Real.log n)*min ((intensity e (1/a)).real (cap f.val ((1+3*RadialShell.η n)/r))) (1/2) ≤ (intensity e (1/a)).real E →
    Real.exp (-K*Real.log n)*min ((intensity e (1/a)).real (cap g.val ((1+3*RadialShell.η n)/s))) (1/2) ≤ (intensity e (1/a)).real F →
    H*Real.sqrt (Real.log n/(n:ℝ)) ≤ angle f.val g.val →
    (intensity e (1/a)).real (E ∩ F)/((intensity e (1/a)).real E*(intensity e (1/a)).real F) ≤ (n:ℝ)⁻¹^8 := by
  have hap : 0 < a := lt_trans (by norm_num) ha
  have hlu : l ≤ u₀ := hlt.le.trans hu₀.le
  have hu₀1 : u₀ < 1 := hu.trans hu1
  let k := min (l/16) ((u-u₀)/4)
  have hk : 0 < k := lt_min (by positivity) (by positivity)
  let c := 2*l*k/Real.pi^2
  have hc : 0 < c := by dsimp [c]; positivity
  let V := Real.exp (8*ShellCaps.A l u₀)
  have hV : 1 ≤ V := Real.one_le_exp (by
    have := ShellCaps.A_pos hl hlu hu₀1
    positivity)
  let P := 27*ShellCaps.C a l u₀
  have hP : 0 < P := mul_pos (by norm_num) (ShellCaps.C_pos hap hl hlu hu₀1)
  let H := Real.sqrt ((2*K+P+9)/c)
  have hH : 0 < H := Real.sqrt_pos.mpr (div_pos (by linarith) hc)
  have hHsq : 2*K+P+9 ≤ c*H^2 := by
    dsimp [H]
    rw [Real.sq_sqrt (by positivity)]
    exact le_of_eq (by field_simp)
  obtain ⟨nS,hnS⟩ := ShellCaps.shell_cost ha.le hl hlt hu₀ hu₀1
  obtain ⟨nD,hnD⟩ := exists_nat_ge (max (4*V) (2*(1/l+1/(1-u^2))/l))
  refine ⟨H,hH,max nS (max nD 2),?_⟩
  intro n hn _ e f g r s hrl hrh hsl hsh E F hE hF he hf hangle
  have hn2 : 2 ≤ n := (le_max_right nD 2).trans ((le_max_right nS _).trans hn)
  have hnS' : nS ≤ n := (le_max_left _ _).trans hn
  have hnD' : nD ≤ n := (le_max_left nD 2).trans ((le_max_right nS _).trans hn)
  have hnd : (nD:ℝ) ≤ n := by exact_mod_cast hnD'
  have hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l := by
    exact (div_le_iff₀ hl).mp ((le_max_right _ _).trans (hnD.trans hnd))
  have hnV : 4*V ≤ (n:ℝ) := (le_max_left _ _).trans (hnD.trans hnd)
  have hr := hnS n hnS' e f r hrl hrh
  have hs := hnS n hnS' e g s hsl hsh
  have hratio := SlotGeometry.ratio e f g hl hu1 (by positivity : 0 ≤ 1/a)
    ((div_lt_one hap).mpr ha) hr.1 hr.2.1 hs.1 hs.2.1 hu.le hk.le
    (min_le_left _ _) (by have := min_le_right (l/16) ((u-u₀)/4); dsimp [k] at *; linarith)
    hdim hV hE hF hr.2.2.1 hs.2.2.1 hr.2.2.2.2.2 hs.2.2.2.2.2 he hf
  exact hratio.trans (SlotGeometry.decay hn2 (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    hc (by positivity : 0 ≤ 4*V) hnV hH.le hHsq hangle)

lemma coarse {n : ℕ} {ε t r s : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (e f g : Sphere n) {E F : Set (Sphere n)}
    (hE : E ⊆ cap f.val r) (hF : F ⊆ cap g.val s)
    (hr : 1/Real.sqrt (1+4*ε) ≤ r) (hs : 1/Real.sqrt (1+4*ε) ≤ s)
    (hangle : 4*Real.sqrt ε < angle f.val g.val) :
    (intensity e t).real (E ∩ F) = 0 := by
  have hdis := CapDisjoint.disjoint hε hε1
    (mem_sphere_zero_iff_norm.mp f.property) (mem_sphere_zero_iff_norm.mp g.property) hr hs hangle
  have hEF : E ∩ F = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    apply Set.disjoint_left.mp hdis
    · exact ⟨mem_sphere_zero_iff_norm.mp x.property,hE hx.1⟩
    · exact ⟨mem_sphere_zero_iff_norm.mp x.property,hF hx.2⟩
  simp [hEF]

end CrossDeployment

end OAI
