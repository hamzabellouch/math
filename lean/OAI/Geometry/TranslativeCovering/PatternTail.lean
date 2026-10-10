import OAI.Geometry.TranslativeCovering.BodyVolume

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

universe u_1 u_2 u_3

namespace PatternTail
open Set Metric MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness PoissonDiagrams
open scoped BigOperators ENNReal Classical
abbrev Space (n : ℕ) := SphericalLaw.Space n

noncomputable def coverEvent {n : ℕ} {J : Type u_1} [Fintype J] (p : J → Space n)
    (a D : ℝ) : Set (PoissonConfig.Config (Sphere n)) :=
  {U | ∀ y ∈ closedBall (0 : Space n) D, ∃ i,y-p i ∈
    RandomBody.body (RadialShell.high a n) (1+3*RadialShell.η n) U}

lemma empty_target {n : ℕ} {J : Type u_2} [Fintype J] (p : J → Space n)
    {a D : ℝ} {y : Space n} (hy : y ∈ closedBall (0 : Space n) D)
    (hz : ¬(relevant p (RadialShell.high a n) y).Nonempty) : coverEvent p a D = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro U hU
  obtain ⟨i,hi⟩ := hU y hy
  exact hz ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,mem_closedBall_zero_iff.mp hi.1⟩⟩

theorem bound {a l u₀ u : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) :
    ∃ K A H : ℝ,0 < K ∧ 0 < A ∧ 0 < H ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (J : Type u_3) [Fintype J] [Nonempty J] (e : Sphere n) (p : J → Space n)
      (D C ε : ℝ) (M : ℕ),
    0 < D → 0 ≤ C → C ≤ (n:ℝ)^2 → 0 < ε → ε ≤ 1 → 2 ≤ M →
    0 < RadialShell.low a n →
    1/Real.sqrt (1+4*ε) ≤ (1+3*RadialShell.η n)/RadialShell.high a n →
    volume (closedBall (0 : Space n) D) ≤ 4*volume
      (roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C) →
    ((TargetSampling.pairs M).card:ℝ)*(12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
      (RadialShell.high a n*(H*Real.sqrt (Real.log n/(n:ℝ)))/D)^(n-1)) < 1/2 →
    (BodyVolume.law e a).real (coverEvent p a D) ≤
      Real.exp (-1/(8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ)+
        10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*
          (12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
            (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1))))) := by
  obtain ⟨K,A,hK,hA,n₁,hconstruct⟩ := PatternWitness.construct ha hl hlt hu₀ hu hu1
  obtain ⟨H,hH,n₂,hfine⟩ := PatternCross.fine ha hl hlt hu₀ hu hu1 hK.le
  refine ⟨K,A,H,hK,hA,hH,max n₁ (max n₂ 3),?_⟩
  intro n hn _ _ J _ _ e p D C ε M hD hC hCn hε hε1 hM hlo hthreshold hlarge hsmall
  have hn3 : 3 ≤ n := (le_max_right n₁ (max n₂ 3)).trans hn |>.trans' (le_max_right n₂ 3)
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hhigh : 0 < RadialShell.high a n := by
    unfold RadialShell.high RadialShell.η
    positivity
  let G := roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C
  let f : ℝ := 12*((n:ℝ)+1)*(Fintype.card J:ℝ)^2*
    (RadialShell.high a n*(4*Real.sqrt ε)/D)^(n-1)
  have hf : 0 ≤ f := by dsimp [f]; positivity
  obtain ⟨x,hx,hinj,hsep,hscore⟩ := TargetGeometry.select p (ξ := 4*Real.sqrt ε)
    (measurable_roundedGood p a D _ _ C) hD hhigh
    (mul_pos hH (Real.sqrt_pos.mpr (div_pos hlog hnp)))
    (mul_pos (by norm_num : (0:ℝ)<4) (Real.sqrt_pos.mpr hε))
    (fun y hy => hy.1) hlarge hM inferInstance hsmall
  by_cases he : ∃ i,¬(relevant p (RadialShell.high a n) (x i)).Nonempty
  · obtain ⟨i,hi⟩ := he
    rw [empty_target p (hx i).1 hi,measureReal_empty]
    exact (Real.exp_pos _).le
  push Not at he
  have hcard (i : Fin M) : (relevant p (RadialShell.high a n) (x i)).card ≤ n^2 := by
    exact_mod_cast (hx i).2.2.1.trans hCn
  let W (i : Fin M) : Certificate e p (x i) a K A C := Classical.choice
    (hconstruct n ((le_max_left _ _).trans hn) J e p (x i) D C hlo (hx i) (he i) (hcard i))
  let ν (i : Fin M) : ℝ := PatternCross.activity (W i)
  have hAC : 0 ≤ A*C := mul_nonneg hA.le hC
  let : Nonempty (Fin M) := ⟨⟨0,by omega⟩⟩
  obtain ⟨S,hSne,hSc,v,hv,hbin⟩ := ActivityBins.exists_bin ν hAC (fun i => by simpa only [ν,PatternCross.activity,neg_mul] using (W i).lower) (fun i => (W i).upper)
  let : Nonempty S := hSne.to_subtype
  let I (i : S) := (W i).P.parts
  let (i : S) : Nonempty (I i) := (W i).nonempty.to_subtype
  let E (i : S) : I i → Set (Sphere n) := (W i).slot
  let bad (i j : S) : Prop := (x i,x j) ∈ TargetGeometry.bad p (RadialShell.high a n) (4*Real.sqrt ε)
  have hc (i j : S) (hij : i ≠ j) :
      diagram (intensity e (1/a)) (E i) (E j) ≤
      if bad i j then (n:ℝ)⁻¹^3*ν i*ν j else 0 := by
    split_ifs with hb
    · exact hfine n ((le_max_right _ _).trans hn |>.trans' (le_max_left _ _))
        e p (x i) (x j) D A C hlo (hx i) (hx j)
        (hsep i j (fun h => hij (Subtype.ext h))) (W i) (W j)
    · exact le_of_eq (PatternCross.coarse e p (x i) (x j) hε.le hε1 hlo hthreshold
        (hx i) (hx j) hb (W i) (W j))
  have hbad := BinSelection.bad_bin (TargetGeometry.bad p (RadialShell.high a n) (4*Real.sqrt ε))
    x S (Nat.cast_nonneg (ActivityBins.count (A*C))) hf
    (by simpa only [Fintype.card_fin] using hSc) hscore
  have hprob := PoissonBinned.bound (rate e (1/a)) (σ n) E
    (fun i j => (W i).measurable_slot j) (fun i j => (W i).positive j) bad
    hv hf (by positivity : 0 ≤ (n:ℝ)⁻¹^3)
    (fun i => hbin i i.property) (fun i => (W i).self) hc hbad
  have hsub : coverEvent p a D ⊆ {U | ∀ i : S,PoissonConfig.witnessCount (E i) U = 0} := by
    intro U hU i
    by_contra hz
    obtain ⟨j,hj⟩ := hU (x i) (hx i).1
    exact (W i).hole U (Nat.pos_of_ne_zero hz) j hj
  have hmeasure := measureReal_mono (μ := BodyVolume.law e a) hsub
  apply (hmeasure.trans hprob).trans
  apply Real.exp_le_exp.mpr
  have hSp : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hMp : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hQp : (0:ℝ) < ActivityBins.count (A*C) := by unfold ActivityBins.count; positivity
  have hdr : Real.exp (2*A*C)/(Fintype.card S:ℝ) ≤
      (ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ) := by
    apply (div_le_div_iff₀ hSp hMp).mpr
    have hh := mul_le_mul_of_nonneg_left hSc (Real.exp_pos (2*A*C)).le
    simpa only [Fintype.card_fin,Fintype.card_coe,mul_assoc,mul_comm,mul_left_comm] using hh
  have hden : 0 < 8*(Real.exp (2*A*C)/(Fintype.card S:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*f) := by
    positivity
  have hdenle : 8*(Real.exp (2*A*C)/(Fintype.card S:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*f) ≤
      8*((ActivityBins.count (A*C):ℝ)*Real.exp (2*A*C)/(M:ℝ)+10*(n:ℝ)⁻¹^3*(ActivityBins.count (A*C):ℝ)^2*f) := by
    gcongr
  simpa only [neg_div] using neg_le_neg (one_div_le_one_div_of_le hden hdenle)
end PatternTail

end OAI
