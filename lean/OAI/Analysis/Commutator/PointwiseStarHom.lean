import Mathlib
import OAI.Analysis.Commutator.CountableFieldHom
import OAI.Analysis.Commutator.DenseRationalStar
import OAI.Analysis.Commutator.StarHomFieldLip
import OAI.Analysis.Commutator.StarHomFieldRaw

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology CStarAlgebra

namespace Kadison.Decomposable

variable {Ω H A : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] [IsFiniteMeasure μ] [NeZero μ]
  [CStarAlgebra A] [TopologicalSpace.SeparableSpace A]

local instance pointwiseStarHomNormedAlgebra : NormedAlgebra ℚ A :=
  NormedAlgebra.restrictScalars ℚ ℂ A

local instance pointwiseStarHomStarModule : StarModule ℚ A where
  star_smul r a := by
    change star ((r:ℂ) • a)=((star r:ℚ):ℂ) • star a
    simp

theorem exists_pointwise_starHom
    (ρ : A →⋆ₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ))
    (hcomm : ∀ a (s : Set Ω) (hs : MeasurableSet s),
      Commute (ρ a) (indicatorOperator (H:=H) μ s hs)) :
    ∃ σ : Ω → A →⋆ₐ[ℂ] (H →L[ℂ] H),
      (∀ a ξ,AEStronglyMeasurable (fun x => σ x a ξ) μ) ∧
      (∀ a (f : Lp H 2 μ),ρ a f =ᵐ[μ] fun x => σ x a (f x)) := by
  classical
  obtain ⟨T,hm,hb,he,ha,hmu,hst,hsc⟩ := exists_starHom_fields μ ρ hcomm
  obtain ⟨S,hcount,hd,hI⟩ := DenseRationalStar.exists_dense_countable A
  let : Countable S := hcount
  have hg := homomorphisms_ae_of_countable_relations μ S hd hI T hb ha hmu hst hsc
  obtain ⟨x₀,hx₀⟩ := hg.exists
  obtain ⟨Φ₀,hΦ₀⟩ := hx₀
  have hex (x : Ω) : ∃ Φ : A →⋆ₐ[ℂ] (H →L[ℂ] H),
      (∃ Ψ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Ψ (a:A)=T (a:A) x) →
        ∀ a : S,Φ (a:A)=T (a:A) x := by
    by_cases hx : ∃ Ψ : A →⋆ₐ[ℂ] (H →L[ℂ] H),∀ a : S,Ψ (a:A)=T (a:A) x
    · obtain ⟨Ψ,hΨ⟩ := hx
      exact ⟨Ψ,fun _ => hΨ⟩
    · exact ⟨Φ₀,fun h => (hx h).elim⟩
  choose σ hσ using hex
  have hσg : ∀ᵐ x ∂μ,∀ a : S,σ x (a:A)=T (a:A) x :=
    hg.mono (fun x hx => hσ x hx)
  have hσae (a : A) : (fun x => σ x a)=ᵐ[μ]T a := by
    obtain ⟨s,hs,hl⟩ := mem_closure_iff_seq_limit.mp (hd a)
    choose b hbs using hs
    have hbl : Tendsto (fun n => (b n:A)) atTop (𝓝 a) := by
      have heq : (fun n => (b n:A))=s := funext hbs
      rwa [heq]
    filter_upwards [hσg,ae_all_iff.mpr (fun n =>
      representation_field_diff_bound μ ρ T hm hb he (b n:A) a)] with x hx hxb
    have ht : Tendsto (fun n => T (b n:A) x) atTop (𝓝 (T a x)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      exact squeeze_zero (fun _ => norm_nonneg _) hxb
        (by simpa using (hbl.sub_const a).norm)
    have hc : Continuous (σ x : A → (H →L[ℂ] H)) :=
      map_continuous (σ x)
    have hlim := (hc.tendsto a).comp hbl
    have heq : (fun n => σ x (b n:A))=(fun n => T (b n:A) x) := funext (fun n => hx (b n))
    change Tendsto (fun n => σ x (b n:A)) atTop (𝓝 (σ x a)) at hlim
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim ht
  refine ⟨σ,?_,?_⟩
  · intro a ξ
    apply (hm a ξ).congr
    filter_upwards [hσae a] with x hx
    exact congrArg (fun U : H →L[ℂ] H => U ξ) hx.symm
  · intro a f
    rw [he a]
    filter_upwards [operator_ae μ (T a) (hm a) (hb a) f,hσae a] with x hx hs
    rw [hx,hs]

end Kadison.Decomposable

end

end
end

end OAI
