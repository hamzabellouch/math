import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare04
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement Pointwise
namespace CompactFamilyDescent
open Set Topology
noncomputable section

 

theorem finite_tests_of_dense_span {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : ι → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (K : Set E) (hK : IsCompact K) (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) :
    ∃ S : Finset ι, ∃ η : ℝ, 0 < η ∧
      ∀ L : E →ₗ[ℂ] ℂ, (∀ f, ‖L f‖ ≤ B * ‖f‖) →
        (∃ f ∈ K, δ ≤ ‖L f‖) → ∃ i ∈ S, η ≤ ‖L (v i)‖ := by
  classical
  let ε := δ / (4 * B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have happ (f : E) : ∃ c : ι →₀ ℂ, dist f (c.sum fun i a => a • v i) < ε := by
    have hf : f ∈ closure (Submodule.span ℂ (Set.range v) : Set E) := by
      rw [← Submodule.topologicalClosure_coe, hv]
      trivial
    obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
    exact ⟨c, hfg⟩
  choose c hc using happ
  let P : E → E := fun f => (c f).sum fun i a => a • v i
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun f => Metric.ball (P f) ε)
    (fun _ => Metric.isOpen_ball) (by
      intro f _
      exact Set.mem_iUnion.mpr ⟨f, hc f⟩)
  let H := 1 + ∑ f ∈ t, ∑ i ∈ (c f).support, ‖c f i‖
  have hH : 0 < H := by
    dsimp [H]
    positivity
  let η := δ / (4 * H)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨t.biUnion (fun f => (c f).support), η, hη, ?_⟩
  intro L hL ⟨f, hf, hlarge⟩
  obtain ⟨g, hg, hfg⟩ := Set.mem_iUnion₂.mp (ht hf)
  have hfg' : dist f (P g) < ε := hfg
  by_contra hno
  push Not at hno
  have hPg : ‖L (P g)‖ ≤ H * η := by
    calc
      _ = ‖∑ i ∈ (c g).support, (c g i) • L (v i)‖ := by
        simp [P, Finsupp.sum, map_sum]
      _ ≤ ∑ i ∈ (c g).support, ‖c g i‖ * ‖L (v i)‖ := by
        simpa only [norm_smul] using norm_sum_le (c g).support (fun i => c g i • L (v i))
      _ ≤ ∑ i ∈ (c g).support, ‖c g i‖ * η := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (hno i (Finset.mem_biUnion.mpr ⟨g, hg, hi⟩)).le
      _ = (∑ i ∈ (c g).support, ‖c g i‖) * η := by rw [Finset.sum_mul]
      _ ≤ H * η := by
        apply mul_le_mul_of_nonneg_right _ hη.le
        have hsum := Finset.single_le_sum (f := fun x => ∑ i ∈ (c x).support, ‖c x i‖) (fun x (_ : x ∈ t) =>
          Finset.sum_nonneg (fun i _ => norm_nonneg (c x i))) hg
        dsimp [H]
        linarith only [hsum]
  have hdist : ‖L (f - P g)‖ < B * ε := by
    calc
      _ ≤ B * ‖f - P g‖ := hL _
      _ < B * ε := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hfg') hB
  have hsum := norm_add_le (L (f - P g)) (L (P g))
  rw [← map_add, sub_add_cancel] at hsum
  have he₁ : B * ε = δ / 4 := by dsimp [ε]; field_simp
  have he₂ : H * η = δ / 4 := by dsimp [η]; field_simp
  rw [he₁] at hdist
  rw [he₂] at hPg
  linarith

variable {X Y P : Type*}

 

theorem continuous_family_descent [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace P] {q : X → Y} (hq : IsOpenQuotientMap q)
    (F : P → C(Y, ℂ))
    (hF : Continuous (fun p : P × X => F p.1 (q p.2))) :
    Continuous (fun p : P × Y => F p.1 p.2) := by
  exact (IsOpenQuotientMap.id.prodMap hq).continuous_comp_iff.mp hF

 

theorem continuous_family_map [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace P] [LocallyCompactSpace Y]
    {q : X → Y} (hq : IsOpenQuotientMap q) (F : P → C(Y, ℂ))
    (hF : Continuous (fun p : P × X => F p.1 (q p.2))) : Continuous F := by
  exact (ContinuousMap.curry ⟨_,continuous_family_descent hq F hF⟩).continuous

 

theorem compact_descended_family [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace P] [LocallyCompactSpace Y]
    {q : X → Y} (hq : IsOpenQuotientMap q) (F : P → C(Y, ℂ))
    (hF : Continuous (fun p : P × X => F p.1 (q p.2)))
    (K : Set P) (hK : IsCompact K) : IsCompact (F '' K) :=
  hK.image (continuous_family_map hq F hF)

section Lipschitz
variable [MetricSpace Y] [CompactSpace Y]

def lipschitzMaps : Set C(Y,ℂ) := {F | ∃ C : NNReal, LipschitzWith C F}

lemma lipschitz_mul (F G : C(Y,ℂ)) {C D : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith D G) :
    LipschitzWith (‖F‖₊ * D + ‖G‖₊ * C) (F*G) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (F x * G x) (F y * G y) ≤ _
  calc
    _ = ‖F x * (G x-G y) + (F x-F y) * G y‖ := by
      rw [dist_eq_norm]; congr 1; ring
    _ ≤ ‖F x‖ * ‖G x-G y‖ + ‖F x-F y‖ * ‖G y‖ := by
      simpa only [norm_mul] using norm_add_le (F x * (G x-G y)) ((F x-F y) * G y)
    _ ≤ ‖F‖ * (D * dist x y) + (C * dist x y) * ‖G‖ := by
      apply add_le_add
      · exact mul_le_mul (F.norm_coe_le_norm x)
          (by simpa only [dist_eq_norm] using hG.dist_le_mul x y) (norm_nonneg _) (norm_nonneg _)
      · exact mul_le_mul (by simpa only [dist_eq_norm] using hF.dist_le_mul x y)
          (G.norm_coe_le_norm y) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul,coe_nnnorm]; ring

 
def lipAlgebra : StarSubalgebra ℂ C(Y,ℂ) where
  carrier := lipschitzMaps
  zero_mem' := ⟨0,LipschitzWith.const 0⟩
  add_mem' := by
    rintro f g ⟨C,hf⟩ ⟨D,hg⟩
    exact ⟨C+D,hf.add hg⟩
  one_mem' := ⟨0,LipschitzWith.const 1⟩
  mul_mem' := by
    rintro f g ⟨C,hf⟩ ⟨D,hg⟩
    exact ⟨_,lipschitz_mul f g hf hg⟩
  algebraMap_mem' z := ⟨0,LipschitzWith.const z⟩
  star_mem' := by
    rintro f ⟨C,hf⟩
    refine ⟨C,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    simpa only [ContinuousMap.star_apply,dist_star_star] using hf.dist_le_mul x y

lemma lipAlgebra_separates : (lipAlgebra (Y := Y)).SeparatesPoints := by
  intro x y hxy
  let F : C(Y,ℂ) := ⟨fun z => (dist z x : ℂ),by fun_prop⟩
  have hl : LipschitzWith 1 F := by
    simpa only [one_mul,F,ContinuousMap.coe_mk,Function.comp_def] using!
      Complex.isometry_ofReal.lipschitzWith.comp (LipschitzWith.dist_left x)
  refine ⟨_,⟨F,⟨1,hl⟩,rfl⟩,?_⟩
  intro h
  have hc : (0 : ℂ) = (dist y x : ℂ) := by
    simpa only [F,ContinuousMap.coe_mk,dist_self,Complex.ofReal_zero] using h
  exact hxy (dist_eq_zero.mp (Complex.ofReal_eq_zero.mp hc.symm)).symm

theorem lipschitzMaps_dense :
    (Submodule.span ℂ (lipschitzMaps (Y := Y))).topologicalClosure = ⊤ := by
  have hs : Submodule.span ℂ (lipschitzMaps (Y := Y)) =
      (lipAlgebra (Y := Y)).toSubalgebra.toSubmodule := by
    change Submodule.span ℂ ((lipAlgebra (Y := Y)).toSubalgebra.toSubmodule : Set C(Y,ℂ)) = _
    exact Submodule.span_eq ((lipAlgebra (Y := Y)).toSubalgebra.toSubmodule)
  rw [hs]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      (lipAlgebra (Y := Y)) lipAlgebra_separates)

 

theorem finite_lipschitz_obstruction (K : Set C(Y,ℂ)) (hK : IsCompact K)
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) :
    ∃ S : Finset {F : C(Y,ℂ) // F ∈ lipschitzMaps}, ∃ η : ℝ, 0 < η ∧
      ∀ L : C(Y,ℂ) →ₗ[ℂ] ℂ, (∀ F, ‖L F‖ ≤ B * ‖F‖) →
        (∃ F ∈ K, δ ≤ ‖L F‖) → ∃ F ∈ S, η ≤ ‖L F.val‖ := by
  apply finite_tests_of_dense_span _ ?_ K hK δ B hδ hB
  simpa only [Subtype.range_coe_subtype,Set.ofPred_mem_eq] using
    (lipschitzMaps_dense (Y := Y))

end Lipschitz
end
end CompactFamilyDescent

namespace UniformSquareObservable
open CubeFaces LeibmanSquare RationalQuotientFunctions CompactFamilyDescent Topology
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Filtration G) (h0 : H.level 0 = ⊤) (Γ : Subgroup G)
    (s : ℕ) (hs0 : 1 ≤ s) (hs : H.level (s+1) = ⊥)

abbrev ReducedSpace :=
  letI := last_normal H h0 hs0 hs
  ((level H h0 1) ⧸ (restricted H h0).level s) ⧸
    ((Γ.prod Γ).comap (level H h0 1).subtype).map
      (QuotientGroup.mk' ((restricted H h0).level s))

def reducedProjection (x : level H h0 1) : ReducedSpace H h0 Γ s hs0 hs := by
  letI := last_normal H h0 hs0 hs
  exact QuotientGroup.mk (QuotientGroup.mk' ((restricted H h0).level s) x)

 
def observable (F : C(G ⧸ Γ,ℂ)) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (p : G × G) : C(ReducedSpace H h0 Γ s hs0 hs,ℂ) := by
  letI := last_normal H h0 hs0 hs
  exact {
  toFun := normalDescend ((restricted H h0).level s)
    ((Γ.prod Γ).comap (level H h0 1).subtype)
    (balanced H h0 Γ F p.1 p.2)
    (balanced_last H h0 Γ F p.1 p.2 s hs0 hs χ hχ hw)
    (balanced_lattice H h0 Γ F p.1 p.2)
  continuous_toFun := continuous_normalDescend _ _ _ _ _
    (continuous_balanced H h0 Γ F p.1 p.2) }

@[simp] lemma observable_apply (F : C(G ⧸ Γ,ℂ)) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (p : G × G) (x : level H h0 1) :
    observable H h0 Γ s hs0 hs F χ hχ hw p
      (reducedProjection H h0 Γ s hs0 hs x) =
      F (QuotientGroup.mk (p.1*x.val.1)) * star (F (QuotientGroup.mk (p.2*x.val.2))) := rfl

 

theorem continuous_observable [LocallyCompactSpace (ReducedSpace H h0 Γ s hs0 hs)]
    (F : C(G ⧸ Γ,ℂ)) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x)) :
    Continuous (observable H h0 Γ s hs0 hs F χ hχ hw) := by
  let := last_normal H h0 hs0 hs
  let N := (restricted H h0).level s
  let L := (Γ.prod Γ).comap (level H h0 1).subtype
  let q : level H h0 1 → ReducedSpace H h0 Γ s hs0 hs :=
    fun x => QuotientGroup.mk (QuotientGroup.mk' N x)
  have hq : IsOpenQuotientMap q :=
    QuotientGroup.isOpenQuotientMap_mk.comp QuotientGroup.isOpenQuotientMap_mk
  apply continuous_family_map hq
  change Continuous (fun p : (G × G) × level H h0 1 =>
    F (QuotientGroup.mk (p.1.1*p.2.val.1)) *
      star (F (QuotientGroup.mk (p.1.2*p.2.val.2))))
  exact (F.continuous.comp (QuotientGroup.continuous_mk.comp
    ((continuous_fst.fst).mul (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))))).mul
      (continuous_star.comp (F.continuous.comp (QuotientGroup.continuous_mk.comp
        ((continuous_fst.snd).mul (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))))))

 

theorem compact_observable_family [LocallyCompactSpace (ReducedSpace H h0 Γ s hs0 hs)]
    (F : C(G ⧸ Γ,ℂ)) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (C : Set G) (hC : IsCompact C) :
    IsCompact (observable H h0 Γ s hs0 hs F χ hχ hw '' (C ×ˢ C)) :=
  (hC.prod hC).image (continuous_observable H h0 Γ s hs0 hs F χ hχ hw)

 

theorem finite_square_tests [TopologicalSpace.MetrizableSpace (ReducedSpace H h0 Γ s hs0 hs)]
    [CompactSpace (ReducedSpace H h0 Γ s hs0 hs)]
    (F : C(G ⧸ Γ,ℂ)) (χ : G → ℂ)
    (hχ : ∀ n ∈ H.level s, ‖χ n‖ = 1)
    (hw : ∀ n ∈ H.level s, ∀ x : G,
      F (QuotientGroup.mk (x*n)) = χ n * F (QuotientGroup.mk x))
    (C : Set G) (hC : IsCompact C) (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) :
    letI := TopologicalSpace.metrizableSpaceMetric (ReducedSpace H h0 Γ s hs0 hs)
    ∃ S : Finset {f : C(ReducedSpace H h0 Γ s hs0 hs,ℂ) //
      f ∈ lipschitzMaps (Y := ReducedSpace H h0 Γ s hs0 hs)},
      ∃ η : ℝ, 0 < η ∧
      ∀ L : C(ReducedSpace H h0 Γ s hs0 hs,ℂ) →ₗ[ℂ] ℂ,
        (∀ f, ‖L f‖ ≤ B * ‖f‖) →
        (∃ a ∈ C, ∃ b ∈ C,
          δ ≤ ‖L (observable H h0 Γ s hs0 hs F χ hχ hw (a,b))‖) →
        ∃ f ∈ S, η ≤ ‖L f.val‖ := by
  let := TopologicalSpace.metrizableSpaceMetric (ReducedSpace H h0 Γ s hs0 hs)
  obtain ⟨S,η,hη,hS⟩ := finite_lipschitz_obstruction _
    (compact_observable_family H h0 Γ s hs0 hs F χ hχ hw C hC) δ B hδ hB
  refine ⟨S,η,hη,?_⟩
  intro L hL ⟨a,ha,b,hb,hab⟩
  exact hS L hL ⟨_,⟨(a,b),⟨ha,hb⟩,rfl⟩,hab⟩

end
end UniformSquareObservable

end
end
end
end

end OAI
