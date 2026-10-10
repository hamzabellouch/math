import OAI.NumberTheory.DirichletL.Descent.GeneratorTransport
import OAI.NumberTheory.DirichletL.Descent.SecondFreshAssembly

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondUnitFrequency (u v : Eisˣ) (k : Eis) : Eis := ((u^4*v:Eisˣ):Eis)*k

lemma secondUnitFrequency_injective (u v : Eisˣ) : Function.Injective (secondUnitFrequency u v) := by
  intro a b hab
  exact mul_left_cancel₀ (Units.ne_zero (u^4*v)) hab

lemma secondUnitFrequency_norm (u v : Eisˣ) (k : Eis) :
    ‖ConcreteTraceCRT.eisEmbedding (secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding k‖ :=
  GaussGeneratorTransport.norm_eisEmbedding_unit_mul (u^4*v) k

lemma secondUnitFrequency_neg (u v : Eisˣ) (k : Eis) :
    secondUnitFrequency u v (-k) = -secondUnitFrequency u v k := by
  simp only [secondUnitFrequency,mul_neg]

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondCanonical_generator_transport
    (F : Finset ι) (Ψ : Eis →* ℂ) (m label d e k : Eis)
    (L D E : Ideal Eis) (u v : Eisˣ)
    (hl : label = (u:Eis)*primaryGenerator L)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E))
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m label (d*e*k) slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m (primaryGenerator L)
        (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k) slots lists a W X := by
  rw [hl,finiteCanonicalMarkedRow_label_transfer,hd]
  congr 1
  unfold secondUnitFrequency
  change (u:Eis)^4*((v:Eis)*(primaryGenerator D*primaryGenerator E)*k) =
    primaryGenerator D*primaryGenerator E*(((u:Eis)^4*(v:Eis))*k)
  ring

theorem secondCanonical_row_norm (D E : Ideal Eis) (u v : Eisˣ) (d e k : Eis)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E)) :
    ‖ConcreteTraceCRT.eisEmbedding
      (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*e*k)‖ := by
  rw [hd]
  have hl : primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k =
      ((u^4*v:Eisˣ):Eis)*(primaryGenerator D*primaryGenerator E*k) := by
    unfold secondUnitFrequency
    ring
  rw [hl,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  have hr : (v:Eis)*(primaryGenerator D*primaryGenerator E)*k =
      (v:Eis)*(primaryGenerator D*primaryGenerator E*k) := by ring
  rw [hr,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem exists_second_generator_sectors (label d e : Eis) (L D E : Ideal Eis)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryGenerator L ≠ 0) (hD : primaryGenerator D ≠ 0) (hE : primaryGenerator E ≠ 0) :
    ∃ u v : Eisˣ, label = (u:Eis)*primaryGenerator L ∧
      d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryGenerator_mul]; exact mul_ne_zero hD hE)
  exact ⟨u,v,hu,by simpa only [primaryGenerator_mul] using hv⟩

end
end SevenEighths.InverseMoment

end OAI
