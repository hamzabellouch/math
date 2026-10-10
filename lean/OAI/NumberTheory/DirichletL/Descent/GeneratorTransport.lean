import OAI.NumberTheory.DirichletL.Descent.Canonical

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_label_transfer (Ψ : Eis →* ℂ) (m a f k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m (a*f) k H S =
      secondChildColumn p hp hcop hg Ψ m f (a^4*k) H S := by
  simp only [secondChildColumn, finiteSquarefreeRow, map_mul, map_pow,
    Finset.prod_mul_distrib, Finset.prod_pow, mul_pow]
  ring

theorem secondChildColumn_puncture_unit (Ψ : Eis →* ℂ) (u : Eisˣ) (m f k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ ((u:Eis)*m) f k H S =
      secondChildColumn p hp hcop hg Ψ m f k H S := by
  have he : Ideal.span {((u:Eis)*m)} = Ideal.span {m} :=
    Ideal.span_singleton_mul_left_unit u.isUnit m
  simp only [secondChildColumn,rowCoprimeMask_congr_span p S he]

theorem secondChildColumn_generator_unit (Ψ : Eis →* ℂ) (u : Eisˣ) (m f d k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ m ((u:Eis)*f) ((u:Eis)*d*k) H S =
      secondChildColumn p hp hcop hg Ψ m f (d*((u:Eis)^5*k)) H S := by
  rw [secondChildColumn_label_transfer]
  congr 1
  ring

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_label_transfer (F : Finset ι) (Ψ : Eis →* ℂ)
    (m a f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (coeff : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m (a*f) k slots lists coeff W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f (a^4*k) slots lists coeff W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_label_transfer]

theorem generator_eq_unit_primary (I : Ideal Eis) (e : Eis)
    (he : Ideal.span {e} = I) (hI : primaryGenerator I ≠ 0) :
    ∃ u : Eisˣ, e = (u:Eis)*primaryGenerator I := by
  have ha : Associated (primaryGenerator I) e :=
    Ideal.span_singleton_eq_span_singleton.mp ((primaryGenerator_spec I hI).1.trans he.symm)
  obtain ⟨u,hu⟩ := ha
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩

lemma normalized_generator_row_norm (u : Eisˣ) (d k : Eis) :
    ‖ConcreteTraceCRT.eisEmbedding (d*((u:Eis)^5*k))‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*k)‖ := by
  have he : d*((u:Eis)^5*k) = ((u^5:Eisˣ):Eis)*(d*k) := by
    change d*((u:Eis)^5*k) = (u:Eis)^5*(d*k)
    ring
  rw [he,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

end
end SevenEighths.InverseMoment

end OAI
