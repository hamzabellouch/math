import OAI.Analysis.FactorGeneration.AmplificationEncoding
import OAI.Analysis.FactorGeneration.Correlation
import OAI.Analysis.FactorGeneration.MatrixGenerators
import OAI.Analysis.FactorGeneration.PerturbationBounds
import OAI.Analysis.FactorGeneration.RelativeGeneration

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Relative generation under represented-factor hypotheses: unitaries in a dense G-delta set satisfy W*(N,u)=M. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ r : N.toStarSubalgebra,IsStarProjection r → r ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ r ∧ r*q=q ∧ q*r=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem relative_generation_at_continuity (u : TraceUnitary τ)
    (hcont : ∀ x : M.toStarSubalgebra,
      ContinuousAt (fun v => projectionNorm (relativeTraceSpace (N := N) τ v) (baseVector τ x)) u) :
    relativeGenerated (N := N) τ u=M := by
  classical
  by_contra hneq
  let Q := relativeGenerated (N := N) τ u
  have hQM : Q ≤ M := relativeGenerated_le τ hNM u
  obtain ⟨z,hz⟩ := exists_unitary_outside hQM hneq
  let xi := subalgebraResidual τ hQM (z : M.toStarSubalgebra)
  let s : ℝ := τ.norm₂ xi
  have hs : 0 < s := subalgebraResidual_norm_pos τ hQM _ hz
  let α : ℝ := min (1/4) (s/32)/2
  have hα : 0 < α := half_pos (lt_min (by norm_num) (by positivity))
  have hq : α < 1/4 := by
    have h := min_le_left (1/4 : ℝ) (s/32)
    dsimp [α] at hα ⊢
    linarith
  have hsmall : α < s/32 := by
    have h := min_le_right (1/4 : ℝ) (s/32)
    dsimp [α] at hα ⊢
    linarith
  have hhalf : α < 1/2 := by linarith
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have he (n : ℕ) := exists_represented_perturbation τ ω hNM hfactor hdiff hirr hsep hω
    u.toUnitary z xi (n+1) (Nat.succ_pos _) α hα hhalf
  choose v t hv ht using he
  let V : ℕ → TraceUnitary τ := fun n => ⟨v n⟩
  have hV : Tendsto V atTop (𝓝 u) := by
    apply (TraceUnitary.tendsto_iff τ atTop V u).mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hv (perturbation_size_tendsto α)
  let F : TraceUnitary τ → ℝ := fun v =>
    projectionNorm (relativeTraceSpace (N := N) τ v) (baseVector τ xi)
  have hFzero : F u=0 := by
    change ‖(vectorOrbitClosure Q.toStarSubalgebra τ.vector).starProjection
      (baseVector τ (subalgebraResidual τ hQM (z : M.toStarSubalgebra)))‖=0
    rw [subalgebraResidual_projection,norm_zero]
  let δ : ℕ → ℝ := fun n => 1/((n+1 : ℕ) : ℝ)
  have hδ : Tendsto δ atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
  let c : ℕ → ℂ := fun n => τ.trace (star xi*relativeUnitaryWord τ hNM (V n) (t n) (n+1))
  have hc (n : ℕ) : ‖c n-((α*s^2/2 : ℝ) : ℂ)‖ ≤
      s*(4*α^2/(1-2*α))+δ n := by
    have hn := ht n
    have hcorr : τ.trace (star xi*(z : M.toStarSubalgebra))=(s : ℂ)^2 :=
      subalgebraResidual_correlation τ hQM (z : M.toStarSubalgebra)
    rw [hcorr] at hn
    have heq : ((α*s^2/2 : ℝ) : ℂ)=(α : ℂ)/2*(s : ℂ)^2 := by
      push_cast
      ring
    rw [heq]
    exact hn
  have hproj (n : ℕ) : ‖c n‖ ≤ F (V n) :=
    relativeUnitaryWord_correlation_le τ hNM (V n) (t n) (n+1) xi
  exact no_continuous_correlated_sequence F (hcont xi) hFzero V hV δ hδ c
    hs hα hq hsmall hc hproj

theorem represented_relative_generation :
    ∃ C : Set (TraceUnitary τ), IsGδ C ∧ Dense C ∧
      ∀ u ∈ C, wstar ((N : Set (H →L[ℂ] H)) ∪ {(u.algebra τ).val})=M.toStarSubalgebra := by
  obtain ⟨C,hC,hd,hcont⟩ := common_relative_projection_continuity_algebra τ hNM hsep
  refine ⟨C,hC,hd,fun u hu => ?_⟩
  exact congrArg VonNeumannAlgebra.toStarSubalgebra
    (relative_generation_at_continuity τ hNM hfactor hdiff hirr hsep u (hcont u hu))

end

/-! Four generators under a faithful normalized vector trace and trace-vector separability. -/
open scoped ComplexStarModule
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem represented_four_selfAdjoint_generators (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ a ∈ M,∃ b ∈ M,∃ c ∈ M,∃ d ∈ M,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ IsSelfAdjoint c ∧ IsSelfAdjoint d ∧
      wstar {a,b,c,d}=M.toStarSubalgebra := by
  obtain ⟨P,hPM,hP,hscalar,a,ha,b,hb,hsa,hsb,hPgen⟩ :=
    exists_irreducible_two_generated_subfactor τ le_rfl hfactor hdiff
      (fun c hc => hfactor c hc) hsep
  have hPfactor (c : P.toStarSubalgebra) (hc : ∀ a : P.toStarSubalgebra,a*c=c*a) :
      ∃ z : ℂ,c=z • (1 : P.toStarSubalgebra) := by
    obtain ⟨z,hz⟩ := hP.factor c hc
    exact ⟨z,by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩
  have hirr (c : M.toStarSubalgebra)
      (hc : ∀ a : P.toStarSubalgebra,coordinateInclusion hPM a*c=c*coordinateInclusion hPM a) :
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) :=
    ⟨τ.trace c,hscalar c (fun a => congrArg Subtype.val (hc a))⟩
  obtain ⟨C,_,hC,hgen⟩ := represented_relative_generation τ hPM hPfactor hP.diffuse hirr hsep
  let : Nonempty (TraceUnitary τ) := ⟨⟨1⟩⟩
  obtain ⟨u,hu⟩ := hC.nonempty
  let v : H →L[ℂ] H := (u.algebra τ).val
  have hv : v ∈ M.toStarSubalgebra := (u.algebra τ).property
  have hvgen : wstar ((P : Set (H →L[ℂ] H)) ∪ {v})=M.toStarSubalgebra := hgen u hu
  refine ⟨a,hPM ha,b,hPM hb,ℜ v,realPart_mem _ hv,ℑ v,imaginaryPart_mem _ hv,
    hsa,hsb,(ℜ v).property,(ℑ v).property,le_antisymm ?_ ?_⟩
  · exact wstar_le (vonNeumann_wotClosed M)
      (by rintro _ (rfl | rfl | rfl | rfl)
          · exact hPM ha
          · exact hPM hb
          · exact realPart_mem _ hv
          · exact imaginaryPart_mem _ hv)
  · let Q := wstar {a,b,(ℜ v : H →L[ℂ] H),(ℑ v : H →L[ℂ] H)}
    have hPQ : P.toStarSubalgebra ≤ Q := by
      rw [← hPgen]
      exact wstar_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢; tauto)
    rw [← hvgen]
    apply wstar_le (wstar_closed _)
    rintro x (hx | rfl)
    · exact hPQ hx
    · apply (mem_iff_parts_mem Q v).mpr
      exact ⟨subset_wstar _ (by simp),subset_wstar _ (by simp)⟩

end

/-! Single generation for the explicit faithful normalized vector-trace
representation with separable trace-vector range. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem represented_two_selfAdjoint_generators (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ a ∈ M,∃ b ∈ M,IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=M.toStarSubalgebra := by
  obtain ⟨E,_,_,_,_,_⟩ := exists_commuting_matrix_extension τ
    (FiniteMatrixStage.scalarStage M).units ⟨0,(FiniteMatrixStage.scalarStage M).positive⟩ hfactor hdiff 2 (by norm_num)
  let N := E.relativeVonNeumann
  let τN := restrictedTrace τ E.relativeVonNeumann_le
  have hsepN : TopologicalSpace.IsSeparable (Set.range (baseVector τN)) := by
    apply hsep.mono
    rintro y ⟨a,rfl⟩
    exact ⟨coordinateInclusion E.relativeVonNeumann_le a,rfl⟩
  obtain ⟨a,ha,b,hb,c,hc,d,hd,hsa,hsb,hsc,hsd,hgen⟩ := represented_four_selfAdjoint_generators
    τN (E.relative_scalar_center 0 hfactor) (E.relative_diffuse 0 hdiff) hsepN
  let a' : E.commutant := E.relativeEquiv.symm ⟨a,ha⟩
  let b' : E.commutant := E.relativeEquiv.symm ⟨b,hb⟩
  let c' : E.commutant := E.relativeEquiv.symm ⟨c,hc⟩
  let d' : E.commutant := E.relativeEquiv.symm ⟨d,hd⟩
  have hs (x : H →L[ℂ] H) (hx : x ∈ N) (h : IsSelfAdjoint x) :
      IsSelfAdjoint (E.relativeEquiv.symm ⟨x,hx⟩) :=
    (show IsSelfAdjoint (⟨x,hx⟩ : N.toStarSubalgebra) from Subtype.ext h.star_eq).map E.relativeEquiv.symm
  exact E.two_generators_of_four_commutant_generators a' b' c' d'
    (hs a ha hsa) (hs b hb hsb) (hs c hc hsc) (hs d hd hsd) hgen

theorem represented_single_generator (τ : TracialRepresentation M)
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    SinglyGenerated M.toStarSubalgebra := by
  obtain ⟨a,ha,b,hb,hsa,hsb,hgen⟩ := represented_two_selfAdjoint_generators τ hfactor hdiff hsep
  exact ⟨a+Complex.I • b,M.add_mem ha (M.smul_mem hb _),(wstar_pack hsa hsb).trans hgen⟩

theorem singlyGenerated_of_tracialRepresentation (hM : IsII1Factor M.toStarSubalgebra)
    (τ : TracialRepresentation M)
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    SinglyGenerated M.toStarSubalgebra := by
  apply represented_single_generator τ _ hM.diffuse hsep
  intro c hc
  obtain ⟨z,hz⟩ := hM.factor c hc
  exact ⟨z,by simpa only [Algebra.algebraMap_eq_smul_one] using hz⟩

end Generator.Tracial

end

end OAI
