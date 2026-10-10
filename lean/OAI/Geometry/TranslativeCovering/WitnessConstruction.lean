import OAI.Geometry.TranslativeCovering.SlotGeometry

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

universe u_1

namespace WitnessConstruction
open Set MeasureTheory SphericalLaw CapCost BlockSets PoissonDiagrams
open scoped BigOperators

theorem shell {a l u₀ u W : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hW : 0 < W) :
    ∃ K A : ℝ,0 < K ∧ 0 < A ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (I : Type u_1) [Fintype I] [DecidableEq I] [Nonempty I],Fintype.card I ≤ n^2 →
    ∀ (e : Sphere n) (axes : I → Sphere n) (r : I → ℝ) (R : ℝ),
    (∀ i,RadialShell.low a n ≤ r i) → (∀ i,r i ≤ RadialShell.high a n) →
    (Fintype.card I:ℝ)+(∑ i,RadialCost.weight n a (r i)) ≤ W*R →
    let μ := intensity e (1/a)
    let caps := fun i => cap (axes i).val ((1+3*RadialShell.η n)/r i)
    ∃ (P : Finpartition (Finset.univ : Finset I)) (anchor : Finset I → I)
      (E : Finset I → Set (Sphere n)),
      (∀ S ∈ P.parts,anchor S ∈ S ∧ MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        E S ⊆ caps (anchor S) ∧
        Real.exp (-K*Real.log n)*clipped μ caps (anchor S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      Real.exp (-A*R) ≤ (∏ S : P.parts,μ.real (E S)) ∧
      (∏ S : P.parts,μ.real (E S)) ≤ 1 ∧
      diagram μ (fun S : P.parts => E S) (fun S : P.parts => E S) ≤
        (∏ S : P.parts,μ.real (E S))^2*Real.exp (2*A*R) := by
  have hap : 0 < a := lt_trans (by norm_num) ha
  have hu₀1 : u₀ < 1 := hu.trans hu1
  have hlu : l ≤ u₀ := hlt.le.trans hu₀.le
  let Cₐ := ShellCaps.C a l u₀
  let H := Real.exp (8*ShellCaps.A l u₀)
  have hCₐ : 0 < Cₐ := ShellCaps.C_pos hap hl hlu hu₀1
  have hH : 1 ≤ H := Real.one_le_exp (by
    have hh := (ShellCaps.A_pos hl hlu hu₀1).le
    dsimp [ShellCaps.A] at hh ⊢
    positivity)
  obtain ⟨K,C,hK,hC,nB,hnB⟩ := SphericalBlocks.blocks hl hlu hu hu1 hH
  obtain ⟨nS,hnS⟩ := ShellCaps.shell_cost ha.le hl hlt hu₀ hu₀1
  refine ⟨K,C*(1+Cₐ)*W,hK,by positivity,max nB nS,?_⟩
  intro n hn _ _ I _ _ _ hcard e axes r R hrlo hrhi hbudget
  dsimp only
  let μ := intensity e (1/a)
  let caps := fun i => cap (axes i).val ((1+3*RadialShell.η n)/r i)
  have hs (i : I) := hnS n ((le_max_right nB nS).trans hn) e (axes i) (r i) (hrlo i) (hrhi i)
  have ht0 : 0 ≤ 1/a := by positivity
  have ht1 : 1/a < 1 := (div_lt_one hap).mpr ha
  obtain ⟨P,b,E,hE,_,hfirst,hrow⟩ := hnB n ((le_max_left nB nS).trans hn)
    I hcard e (1/a) ht0 ht1 axes (fun i => (1+3*RadialShell.η n)/r i)
    (fun i => (hs i).1) (fun i => (hs i).2.1) (fun i => (hs i).2.2.1)
  have hcost : ∑ i,cost μ caps i ≤ Cₐ*(∑ i,RadialCost.weight n a (r i)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hs i).2.2.2.1
  have hw : 0 ≤ ∑ i,RadialCost.weight n a (r i) := Finset.sum_nonneg fun i _ =>
    (by norm_num : (0:ℝ) ≤ 1).trans (RadialCost.weight_ge_one n a (r i))
  have hm : 0 ≤ (Fintype.card I:ℝ) := Nat.cast_nonneg _
  have hbudget' : (Fintype.card I:ℝ)+∑ i,cost μ caps i ≤ (1+Cₐ)*W*R := by
    have hx := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 1+Cₐ)
    have hmc := mul_nonneg hCₐ.le hm
    nlinarith only [hcost,hw,hx,hmc]
  have hfirst' : ∑ S ∈ P.parts,Real.log (1+(μ.real (E S))⁻¹) ≤ (C*(1+Cₐ)*W)*R := by
    have hh := mul_le_mul_of_nonneg_left hbudget' hC.le
    exact hfirst.trans (by convert hh using 1 ; ring)
  have hrow' : ∑ S ∈ P.parts,Real.log (1+∑ T ∈ P.parts.erase S,Blocks.weight μ (E S) (E T)) ≤ (C*(1+Cₐ)*W)*R := by
    have hh := mul_le_mul_of_nonneg_left hbudget' hC.le
    exact hrow.trans (by convert hh using 1 ; ring)
  obtain ⟨hν,hν1,hD⟩ := WitnessBlocks.certificates P.parts μ E
    (fun S hS => (hE S hS).2.2.2.2.2.1)
    (fun S hS => (hE S hS).2.2.2.2.2.2.trans (by norm_num)) hfirst' hrow'
  refine ⟨P,b,E,?_,?_,hν1,?_⟩
  · intro S hS
    obtain ⟨hb,hm,hmeas,hsub,hslot,hpos,hle⟩ := hE S hS
    exact ⟨hb,hmeas,hsub,fun x hx => (mem_iInter₂.mp (hsub hx)) (b S) hb,hslot,hpos,hle⟩
  · simpa only [neg_mul] using hν
  · dsimp [μ] at hD ⊢
    convert hD using 1 ; ring_nf

end WitnessConstruction

end OAI
