import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥) (hcomm : H.level 2=_root_.commutator G)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

 

def compatibleMetricHomeomorph : @Homeomorph (G⧸Γ) (G⧸Γ)
    (QuotientGroup.instTopologicalSpace Γ) mtr.toUniformSpace.toTopologicalSpace := by
  refine @Homeomorph.mk _ _ (QuotientGroup.instTopologicalSpace Γ)
    mtr.toUniformSpace.toTopologicalSpace (Equiv.refl _) ?_ ?_
  · rw [htop]; exact continuous_id
  · rw [htop]; exact continuous_id

local instance squareInduction04MetricProducerTopology : TopologicalSpace (G⧸Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hcomm hqbound hq2 hq hΓ htop in
 

theorem quadratic_metric_producer
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ P : ℝ[X], P.natDegree ≤ 2 ∧ (∀ z : ℤ, P.eval (z:ℝ)=(ξ (f z)).toAdd) ∧
          ∀ j : ℕ, 0<j → ∃ z : ℤ, |P.coeff j-z| ≤ A/(N:ℝ)^j := by
  classical
  let hCQ : @CompactSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) := quotient_compact c Γ hΓ
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨K,hK,hunit⟩ := FourierObstruction.compact_superset_unit_lipschitz (G⧸Γ)
  let e0 := @ContinuousMap.mk (G⧸Γ) (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)
    mtr.toUniformSpace.toTopologicalSpace (fun x => x) (by rw [htop]; exact @continuous_id _ (QuotientGroup.instTopologicalSpace Γ))
  let pull := @ContinuousMap.compCLM (G⧸Γ) (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ)
    mtr.toUniformSpace.toTopologicalSpace ℂ ℂ _ _ _ _ _ _ e0
  have hK' : IsCompact (pull '' K) := hK.image pull.continuous
  obtain ⟨U,A,hA,hprod⟩ := quadratic_compact_all_lengths c hsk H h0 h1 hs hcomm
    q hqbound hq2 hq Γ hΓ μ (pull '' K) hK' δ hδ
  refine ⟨U,A,hA,?_⟩
  intro N hN f hf ⟨F,hFL,hFn,hdisc⟩
  apply hprod N hN f hf
  refine ⟨pull F,⟨F,hunit F hFL hFn,rfl⟩,?_⟩
  change δ ≤ ‖mean N (fun k => F (QuotientGroup.mk (f k)))-(∫ x,F x ∂μ)‖
  exact hdisc

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace LeibmanSquare
open CubeFaces CubePolynomials RationalFactorPeriods BinomialDifference
variable {G : Type*} [Group G]

 

lemma character_binomial_expansion (H : Filtration G) (s : ℕ)
    (hs : H.level (s+1)=⊥) {f : ℤ→G} (hf : Polynomial H 0 f)
    (χ : G→*Multiplicative ℝ) (P : ℝ[X])
    (hPe : ∀ n : ℤ, P.eval (n:ℝ)=(χ (f n)).toAdd) :
    ∀ n : ℤ, (χ (f n)).toAdd =
      ∑ j : Fin (s+1), coefficient ℝ j.val P * (Ring.choose n j.val : ℤ) := by
  obtain ⟨a,ha,he⟩ := NilpotentTaylor.exists_taylor (by simpa using hs)
    (cube_mem_of_polynomial H hf)
  rw [word_eq_orderedWord] at he
  let b : Fin (s+1)→G := fun j => a j.val
  have hp : P=wordCharacterPolynomial χ b (fun j => j.val) := by
    apply Polynomial.eq_of_eval_nat_eq
    intro n
    rw [← Int.cast_natCast (R:=ℝ) n,hPe,wordCharacterPolynomial_eval]
    exact congrArg (fun u => (χ (u (n:ℤ))).toAdd) he
  have hcoef (j : Fin (s+1)) :
      coefficient ℝ j.val (wordCharacterPolynomial χ b (fun j => j.val))=(χ (b j)).toAdd := by
    simpa only [Nat.add_zero] using coefficient_word χ b 0 j
  intro n
  rw [← hPe n,hp,wordCharacterPolynomial,eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_mul,eval_C,choosePolynomial_int]
  exact congrArg (fun r : ℝ => r*(Ring.choose n j.val:ℤ)) (hcoef j).symm

end LeibmanSquare
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
open scoped BigOperators
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus RationalTailCoordinates UnitAddTorus
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable [∀ i, (H.level i).Normal]
variable (hs : H.level 3=⊥) (hcomm : H.level 2=_root_.commutator G)
variable (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ t+d) (hq2 : q 2=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [hBorel : @BorelSpace (G⧸Γ) (QuotientGroup.instTopologicalSpace Γ) inferInstance]
variable [mtr : MetricSpace (G⧸Γ)]
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

local instance squareInduction04BinomialTopology : TopologicalSpace (G⧸Γ) :=
  mtr.toUniformSpace.toTopologicalSpace

include hsk h0 h1 hs hcomm hqbound hq2 hq hΓ htop in
 

theorem quadratic_leibman_binomial
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
    letI : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧
      ∀ N : ℕ, 0<N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f →
      (∃ F : C(G⧸Γ,ℂ), LipschitzWith 1 F ∧ ‖F‖≤1 ∧
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖) →
      ∃ ξ∈U, ξ≠1 ∧ Continuous ξ ∧ (∀ g∈Γ, ∃ z : ℤ, (ξ g).toAdd=z) ∧
        ∃ b : Fin (t+d)→ℤ, b≠0 ∧ (∀ i, |(b i:ℝ)|≤A) ∧ (∀ i, t ≤ i.val → b i=0) ∧
          (∀ g : G, (ξ g).toAdd=∑ i, c.coord g i*(b i:ℝ)) ∧
        ∃ α : ℕ→ℝ, (∀ j : ℕ, 2<j → α j=0) ∧
          (∀ z : ℤ, (ξ (f z)).toAdd=∑ j : Fin 3, α j.val*(Ring.choose z j.val:ℤ)) ∧
          ∀ j : ℕ, 0<j → (N:ℝ)^j*‖(α j : UnitAddCircle)‖≤A := by
  classical
  let : CompactSpace (G⧸Γ) := metric_compact c Γ hΓ mtr htop
  let : BorelSpace (G⧸Γ) := metric_borelSpace Γ mtr htop
  obtain ⟨U,C,hC,hprod⟩ := quadratic_metric_producer c hsk H h0 h1 hs hcomm
    q hqbound hq2 hq Γ hΓ htop μ δ hδ
  let S : ℝ := ∑ ξ∈U, ∑ i, |(ξ (axis c i 1)).toAdd|
  have hS : 0≤S := Finset.sum_nonneg (fun ξ _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  let A : ℝ := 1+S+BinomialDifference.conversionBound 2*C
  have hconv : 0<BinomialDifference.conversionBound 2*C :=
    mul_pos (BinomialDifference.conversionBound_pos 2) hC
  have hA : 0<A := by dsimp [A]; linarith
  refine ⟨U,A,hA,?_⟩
  intro N hN f hf hdisc
  obtain ⟨ξ,hξ,hξ0,hξc,hξΓ,P,hP,hPe,hPc⟩ := hprod N hN f hf hdisc
  obtain ⟨b,hb⟩ := integer_character_coordinates c hsk ξ Γ hΓ hξc hξΓ
  have hbi (i : Fin (t+d)) : (b i:ℝ)=(ξ (axis c i 1)).toAdd := by
    rw [hb]
    simp [coord_axis,Pi.single_apply]
  refine ⟨ξ,hξ,hξ0,hξc,hξΓ,b,?_,?_,?_,hb,
    fun j => BinomialDifference.coefficient ℝ j P,?_,?_,?_⟩
  · intro hb0
    apply hξ0
    ext g
    apply Multiplicative.toAdd.injective
    change (ξ g).toAdd=0
    rw [hb,hb0]
    simp
  · intro i
    have h1 : |(ξ (axis c i 1)).toAdd| ≤ ∑ j, |(ξ (axis c j 1)).toAdd| :=
      Finset.single_le_sum (f := fun j : Fin (t+d) => |(ξ (axis c j 1)).toAdd|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 : (∑ j, |(ξ (axis c j 1)).toAdd|)≤S :=
      Finset.single_le_sum (f := fun χ : G→*Multiplicative ℝ => ∑ j, |(χ (axis c j 1)).toAdd|) (fun χ _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) hξ
    rw [hbi]
    dsimp [A]
    linarith
  · intro i hi
    have hai : axis c i 1∈H.level 2 := by
      apply (hq 2 _).mpr
      intro j hj
      have hji : j≠i := by intro he; subst j; rw [hq2] at hj; omega
      simp [coord_axis,hji]
    have halt : ξ (axis c i 1)=1 := Abelianization.commutator_subset_ker ξ (hcomm ▸ hai)
    apply Int.cast_injective (α:=ℝ)
    rw [hbi,halt]
    change (0:ℝ)=(0:ℤ)
    norm_num
  · intro j hj
    exact BinomialDifference.coefficient_eq_zero ℝ j P (hP.trans_lt hj)
  · exact character_binomial_expansion H 2 hs hf ξ P hPe
  · intro j hj
    have hNr : 1≤(N:ℝ) := by exact_mod_cast hN
    have hbnd := BinomialDifference.coefficient_bound 2 1 P hP (N:ℝ) C hNr hC.le
      (fun i hi => hPc i hi) j hj
    apply hbnd.trans
    dsimp [A]
    linarith

end SquareInduction
end
end
 

 
section
noncomputable section
open scoped BigOperators
namespace RationalCharacterFirst
open RationalLattice IntegerHyperplane MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

 

theorem exists_strict_refined_integer_cover
    (c : RealCoordinates G (n+1)) (χ : G→*Multiplicative ℝ)
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
    (hcont : Continuous χ) (hz : ∀ g∈Γ, ∃ z : ℤ, (χ g).toAdd=z)
    (H : Subgroup G) (r : ℕ)
    (hH : ∀ g : G, g∈H ↔ ∀ i : Fin (n+1), i.val<r → c.coord g i=0)
    (hne : χ.comp H.subtype≠1) :
    ∃ Λ : Subgroup G, ∃ e : RealCoordinates G (n+1), SecondKind e ∧
      (∀ g : G, g∈Λ ↔ ∀ i, ∃ z : ℤ, e.coord g i=z) ∧
      Λ≤Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧ r+1≤n+1 ∧
      (∀ g : G, g∈H⊓χ.ker ↔ ∀ i : Fin (n+1), i.val<r+1 → e.coord g i=0) ∧
      ∀ K : Subgroup G, ∀ s : ℕ, s≤n+1 →
        (∀ g : G, g∈K ↔ ∀ i : Fin (n+1), i.val<s → c.coord g i=0) →
        ∃ u : ℕ, u≤n+1 ∧ ∀ g : G, g∈K⊓χ.ker ↔
          ∀ i : Fin (n+1), i.val<u → e.coord g i=0 := by
  obtain ⟨k,hk⟩ := integer_character_expCoordinates c Γ hΓ χ hcont hz
  have hk0 : k≠0 := by
    intro he
    apply hne
    ext g
    apply Multiplicative.toAdd.injective
    change (χ g.val).toAdd=0
    rw [hk,he]
    simp
  obtain ⟨p,hp,hlast⟩ := exists_last_nonzero k hk0
  have he : ∀ g : G, (χ g).toAdd=form k ((secondCoordinates c).coord g) := by
    intro g
    rw [hk]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hrp : r≤p.val := by
    by_contra hrp
    apply hne
    ext g
    apply Multiplicative.toAdd.injective
    change (χ g.val).toAdd=0
    rw [he]
    change (∑ i, (k i:ℝ)*(secondCoordinates c).coord g.val i)=0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hir : i.val<r
    · rw [(secondCoordinates_adapted c H r hH g.val).mp g.property i hir,mul_zero]
    · rw [hlast i (by change p.val < i.val; omega),Int.cast_zero,zero_mul]
  let d := characterFirstCoordinates (secondCoordinates c) χ k p hp he hlast
  have hdpoly : ∀ i, RationalPolynomialMap.IsPolynomial
      (fun x : Fin (n+1)→ℝ => c.coord (d.coord.symm x) i) := by
    intro i
    change RationalPolynomialMap.IsPolynomial (fun x => c.coord (expProduct c (splitLift k p x)) i)
    exact polynomialMap_expProduct c (fun j => splitLift_polynomial k p j) i
  obtain ⟨Λ,e,hΛ,hle,hindex,hzero⟩ := exists_integer_sublattice c d (MonoidHom.id G)
    hdpoly Γ hΓ continuous_id Function.injective_id
  have hadapt (K : Subgroup G) (s : ℕ)
      (hK : ∀ g : G, g∈K ↔ ∀ i : Fin (n+1), i.val<s → c.coord g i=0) :
      ∀ g : G, g∈K⊓χ.ker ↔ ∀ i : Fin (n+1), i.val<deletedCutoff p s+1 → e.coord g i=0 := by
    intro g
    rw [characterFirst_adapted (secondCoordinates c) χ k p hp he hlast K s
      (secondCoordinates_adapted c K s hK)]
    exact forall_congr' (fun i => imp_congr_right (fun _ => (hzero g i).symm))
  refine ⟨Λ,secondCoordinates e,secondCoordinates_secondKind e,
    expCoordinates_lattice e Λ hΛ,hle,hindex,by omega,?_,?_⟩
  · have hd : deletedCutoff p r+1=r+1 := by simp [deletedCutoff,not_lt.mpr hrp]
    exact secondCoordinates_adapted e (H⊓χ.ker) (r+1) (by simpa only [hd] using hadapt H r hH)
  · intro K s hs hK
    refine ⟨deletedCutoff p s+1,?_,secondCoordinates_adapted e (K⊓χ.ker) _ (hadapt K s hK)⟩
    unfold deletedCutoff
    split_ifs <;> omega

end RationalCharacterFirst

end
end
end
end
end

end OAI
