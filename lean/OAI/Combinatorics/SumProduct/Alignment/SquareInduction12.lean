import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.SquareInduction11
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
namespace SquareInduction
open CubeFaces LeibmanSquare RationalLattice MalcevCharacters MeasureTheory PolynomialWeyl
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
 

theorem degree_vertical_unbounded_rank_any {n d : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
    (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
    (s : ℕ) (hs2 : 2 ≤ s) (hs : H.level (s+1)=⊥) [∀ i, (H.level i).Normal]
    (q : ℕ→ℕ) (hqbound : ∀ k, q k ≤ n)
    (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin n, i.val<q k → c.coord g i=0)
    (hrank : n-q 2=d+1)
    (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
    [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
    (ID : DegreeStatement (s-1)) (IH : DegreeRankStatement G s n d)
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (F : C(G⧸Γ,ℂ)) (hF : ∀ x, ‖F x‖ ≤ 1) (hF0 : (∫ x,F x ∂μ)=0) (χ : G→ℂ)
    (hχ : ∀ a∈H.level s, ‖χ a‖=1)
    (hw : ∀ a∈H.level s, ∀ x : G, F (QuotientGroup.mk (x*a))=χ a*F (QuotientGroup.mk x))
    (z : G) (hz : z∈H.level s) (hχz : χ z≠1) (δ : ℝ) (hδ : 0<δ) :
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, Polynomial H 0 f → f 0=1 →
      δ ≤ ‖mean N (fun k => F (QuotientGroup.mk (f k)))‖ →
        ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ := by
  have hn : n=q 2+(d+1) := by have := hqbound 2; omega
  subst n
  exact degree_vertical_unbounded_of_rank c hsk H h0 h1 s hs2 hs q hqbound rfl hq Γ hΓ
    ID IH μ F hF hF0 χ hχ hw z hz hχz δ hδ

end SquareInduction
end
end
 

 
section
noncomputable section
namespace MalcevPrefixQuotient
open RationalLattice MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r d : ℕ} (c : RealCoordinates G (r+d)) (hsk : SecondKind c)
variable (N : Subgroup G) [N.Normal]
variable (hN : ∀ g : G, g∈N ↔ ∀ i : Fin (r+d), i.val<r → c.coord g i=0)

omit [IsTopologicalGroup G] in
lemma quotient_axis [IsTopologicalGroup G] (i : Fin r) (t : ℝ) :
    axis (quotientChart c (Nat.le_add_right r d) N hN) i t =
      QuotientGroup.mk' N (axis c (embed (Nat.le_add_right r d) i) t) := by
  classical
  apply (quotientChart c (Nat.le_add_right r d) N hN).coord.injective
  ext j
  rw [coord_axis]
  change (Pi.single i t : Fin r→ℝ) j=c.coord (axis c (embed (Nat.le_add_right r d) i) t) (embed (Nat.le_add_right r d) j)
  rw [coord_axis]
  simp only [Pi.single_apply]
  have he : embed (Nat.le_add_right r d) j=embed (Nat.le_add_right r d) i ↔ j=i := by
    constructor
    · intro h; exact Fin.ext (congrArg (fun x : Fin (r+d) => x.val) h)
    · intro h; rw [h]
  simp only [he]

include hsk in
 

theorem quotient_secondKind : SecondKind (quotientChart c (Nat.le_add_right r d) N hN) where
  axis_add i s t := by
    simp only [quotient_axis,hsk.axis_add,map_mul]
  ordered x := by
    induction x using Quotient.inductionOn with | h g =>
      change QuotientGroup.mk' N g = _
      conv_lhs => rw [hsk.ordered g,map_list_prod,List.map_ofFn,List.ofFn_add,List.prod_append]
      have htail : (List.ofFn (fun i : Fin d => QuotientGroup.mk' N
          (axis c (Fin.natAdd r i) (c.coord g (Fin.natAdd r i))))).prod=1 := by
        have he : (fun i : Fin d => QuotientGroup.mk' N
            (axis c (Fin.natAdd r i) (c.coord g (Fin.natAdd r i))))=fun _ => (1:G⧸N) := by
          funext i
          apply (QuotientGroup.eq_one_iff _).mpr
          apply (hN _).mpr
          intro j hj
          rw [coord_axis]
          have hne : j≠Fin.natAdd r i := by
            intro h
            have := congrArg Fin.val h
            simp only [Fin.val_natAdd] at this
            omega
          simp [hne]
        simp only [he]
        simp
      simp only [Function.comp_def]
      rw [htail,mul_one]
      congr 1
      apply congrArg List.ofFn
      funext i
      rw [quotient_axis]
      rfl

end MalcevPrefixQuotient
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open AbelianMalcevTorus
open RationalLattice MalcevCharacters CubeFaces LeibmanSquare MeasureTheory RationalQuotientFunctions
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {r d : ℕ} (c : RealCoordinates G (r+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤)
variable (s : ℕ) (hs1 : 1 ≤ s) (hs : H.level (s+1)=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hqs : q s=r)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (r+d), i.val<q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs1 hs hqs hq hΓ in
 

omit [∀ i, (H.level i).Normal] in
theorem degree_quotient_observable [∀ i, (H.level i).Normal] (IH : DegreeStatement (s-1))
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (F : C(G⧸Γ,ℂ)) (hF : ∀ g a, a∈H.level s → F (QuotientGroup.mk (g*a))=F (QuotientGroup.mk g))
    (δ : ℝ) (hδ : 0<δ) :
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
      ∀ L : ℕ, N₀ ≤ L → ∀ f : ℤ→G, Polynomial H 0 f →
      δ ≤ ‖FourierObstruction.discrepancy μ L (fun k => QuotientGroup.mk (f k)) F‖ →
        ∃ χ∈U, DegreeCharacterData s Γ A L f χ := by
  classical
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let N := H.level s
  let : N.Normal := Subgroup.normal_of_le_center (last_central_ambient H h1 s hs)
  have hr := Nat.le_add_right r d
  have hN : ∀ g : G, g∈N ↔ ∀ i : Fin (r+d), i.val<r → c.coord g i=0 :=
    fun g => by simpa only [hqs] using hq s g
  let cQ := MalcevPrefixQuotient.quotientChart c hr N hN
  let ΓQ := Γ.map (QuotientGroup.mk' N)
  have hΓQ : ∀ g : G⧸N, g∈ΓQ ↔ ∀ i, ∃ z : ℤ, cQ.coord g i=z :=
    MalcevPrefixQuotient.quotient_lattice c hr N hN Γ hΓ
  have hskQ : SecondKind cQ := MalcevPrefixQuotient.quotient_secondKind c hsk N hN
  let : MetricSpace ((G⧸N)⧸ΓQ) := coordinateQuotientMetric cQ ΓQ hΓQ
  let : CompactSpace ((G⧸N)⧸ΓQ) := quotient_compact cQ ΓQ hΓQ
  let : MeasurableSpace ((G⧸N)⧸ΓQ) := borel _
  let : BorelSpace ((G⧸N)⧸ΓQ) := ⟨rfl⟩
  let Q := quotientMap N Γ
  have hQ : Continuous Q := continuous_quotientMap N Γ
  let ν := Measure.map Q μ
  let : IsProbabilityMeasure ν := inferInstance
  let : SMulInvariantMeasure (G⧸N) ((G⧸N)⧸ΓQ) ν := CentralQuotientAction.invariant_quotientMap N Γ μ
  obtain ⟨FQ,hFQ,_⟩ := existsUnique_normalDescend N Γ
    (⟨fun g => F (QuotientGroup.mk g),F.continuous.comp QuotientGroup.continuous_mk⟩ : C(G,ℂ)) hF
    (fun g a ha => congrArg F (QuotientGroup.mk_mul_of_mem g ha))
  have hFQall : ∀ x : G⧸Γ, FQ (Q x)=F x := by
    intro x
    induction x using Quotient.inductionOn with | h g => exact hFQ g
  let HQ := mapFiltration H (QuotientGroup.mk' N)
  have hsQ : HQ.level ((s-1)+1)=⊥ := by
    rw [Nat.sub_add_cancel hs1]
    apply le_antisymm ?_ bot_le
    rintro g ⟨x,hx,rfl⟩
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have h0Q : HQ.level 0=⊤ := by
    change (H.level 0).map _=⊤
    rw [h0,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have h1Q : HQ.level 1=⊤ := by
    change (H.level 1).map _=⊤
    rw [h1,Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  let qQ := fun k => min (q k) r
  have hqQ : ∀ k (g : G⧸N), g∈HQ.level k ↔ ∀ i : Fin r, i.val<qQ k → cQ.coord g i=0 := by
    intro k g
    change g ∈ (H.level k).map (QuotientGroup.mk' N) ↔ _
    rw [MalcevPrefixQuotient.quotient_adapted c hr N hN (H.level k) (q k) (hq k)]
    constructor
    · intro h i hi; exact h i (lt_of_lt_of_le hi (min_le_left _ _))
    · intro h i hi; exact h i (lt_min hi i.isLt)
  obtain ⟨U,A,hA,N₀,hN₀,hprod⟩ := IH (G⧸N) r r cQ hskQ HQ h0Q h1Q hsQ
    qQ (fun k => min_le_right _ _) hqQ (Nat.sub_le _ _) ΓQ hΓQ ν {FQ} isCompact_singleton δ hδ
  let liftχ : (G⧸N →* Multiplicative ℝ) → (G→*Multiplicative ℝ) := fun χ => χ.comp (QuotientGroup.mk' N)
  refine ⟨U.image liftχ,A,hA,N₀,hN₀,?_⟩
  intro L hL f hf hdisc
  have hint : (∫ x, FQ x ∂ν)=(∫ x,F x ∂μ) := by
    rw [show ν=Measure.map Q μ from rfl,integral_map hQ.measurable.aemeasurable FQ.continuous.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hFQall
  have hdiscQ : δ ≤ ‖FourierObstruction.discrepancy ν L
      (fun k => QuotientGroup.mk (QuotientGroup.mk' N (f k))) FQ‖ := by
    change δ ≤ ‖PolynomialWeyl.mean L (fun k => FQ (QuotientGroup.mk (QuotientGroup.mk' N (f k))))-(∫ x,FQ x ∂ν)‖
    simp only [hFQ,hint]
    exact hdisc
  obtain ⟨χ,hχ,hχ0,hχc,hχΓ,P,hP,hPe,hPc⟩ := hprod L hL (fun z => QuotientGroup.mk' N (f z))
    (polynomial_map H (QuotientGroup.mk' N) hf) ⟨FQ,Set.mem_singleton FQ,hdiscQ⟩
  refine ⟨liftχ χ,Finset.mem_image.mpr ⟨χ,hχ,rfl⟩,?_,
    hχc.comp QuotientGroup.continuous_mk,fun g hg => hχΓ _ ⟨g,hg,rfl⟩,
    P,hP.trans (Nat.sub_le _ _),hPe,hPc⟩
  intro he
  apply hχ0
  apply MonoidHom.ext
  intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
  exact congrArg (fun ψ : G→*Multiplicative ℝ => ψ g) he

end SquareInduction
end
end
 

 
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
namespace SquareInduction
open CubeFaces CubePolynomials LeibmanSquare RationalLattice MalcevCharacters
open MeasureTheory PolynomialWeyl AbelianMalcevTorus MalcevCentralTorus RationalTailCoordinates UnitAddTorus
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {t d : ℕ} (c : RealCoordinates G (t+d)) (hsk : SecondKind c)
variable (H : Filtration G) (h0 : H.level 0=⊤) (h1 : H.level 1=⊤) (s : ℕ) (hs1 : 1 ≤ s) (hs : H.level (s+1)=⊥)
variable [∀ i, (H.level i).Normal]
variable (q : ℕ→ℕ) (hq2 : q s=t)
variable (hq : ∀ k (g : G), g∈H.level k ↔ ∀ i : Fin (t+d), i.val < q k → c.coord g i=0)
variable (Γ : Subgroup G) (hΓ : ∀ g : G, g∈Γ ↔ ∀ i, ∃ z : ℤ, c.coord g i=z)
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]

include hsk h0 h1 hs1 hs hq2 hq hΓ in
 

theorem degree_zero_weight_observable (ID : DegreeStatement (s-1))
    (μ : Measure (G⧸Γ)) [IsProbabilityMeasure μ] [SMulInvariantMeasure G (G⧸Γ) μ]
    (δ : ℝ) (hδ : 0<δ) :
    letI : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
    letI : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
    let htail : ∀ g : G, g∈H.level s ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
      fun g => by simpa only [hq2] using hq s g
    letI := tailAction c hsk (H.level s) Γ (last_central_ambient H h1 s hs) htail hΓ
    ∀ F : C(G⧸Γ,ℂ), TorusVerticalFourier.HasWeight (0 : Fin d→ℤ) F →
      ∃ U : Finset (G→*Multiplicative ℝ), ∃ A : ℝ, 0<A ∧ ∃ N₀ : ℕ, 0<N₀ ∧
        ∀ N : ℕ, N₀ ≤ N → ∀ f : ℤ→G, LeibmanSquare.Polynomial H 0 f → f 0=1 →
        δ ≤ ‖FourierObstruction.discrepancy μ N (fun k => QuotientGroup.mk (f k)) F‖ →
          ∃ ξ∈U, DegreeCharacterData s Γ A N f ξ := by
  classical
  let : MetricSpace (G⧸Γ) := coordinateQuotientMetric c Γ hΓ
  let : CompactSpace (G⧸Γ) := quotient_compact c Γ hΓ
  let htail : ∀ g : G, g∈H.level s ↔ ∀ i : Fin (t+d), i.val < t → c.coord g i=0 :=
    fun g => by simpa only [hq2] using hq s g
  let hcent := last_central_ambient H h1 s hs
  let := tailAction c hsk (H.level s) Γ hcent htail hΓ
  dsimp only
  intro F hw
  have hF : ∀ g a, a∈H.level s → F (QuotientGroup.mk (g*a))=F (QuotientGroup.mk g) := by
    intro g a ha
    have he := hw (torusProjection (tailCoordinates c (H.level s) htail) ⟨a,ha⟩) (QuotientGroup.mk g)
    rw [tailProjection_vadd c hsk (H.level s) Γ hcent htail hΓ] at he
    simpa only [mFourier_zero,ContinuousMap.one_apply,one_mul] using he
  obtain ⟨U,A,hA,M,hM,hprod⟩ := degree_quotient_observable c hsk H h0 h1 s hs1 hs
    q hq2 hq Γ hΓ ID μ F hF δ hδ
  refine ⟨U,A,hA,M,hM,?_⟩
  intro N hN f hf _ hdisc
  exact hprod N hN f hf hdisc

end SquareInduction

end
end
end
end
end

end OAI
