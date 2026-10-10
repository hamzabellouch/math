import OAI.InformationTheory.Entanglement.TraceContractivity

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n e : Type} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]

def eraseComplement (i₀ : n) : Map (n⊕e) n :=
  ad ((coord (Sum.inl : n → n⊕e))ᴴ)+∑ j : e, ad (Matrix.single i₀ (Sum.inr j) 1)
omit [Fintype n] in
lemma single_ad (i : n) (j : e) (A : Mat e) :
    ad (Matrix.single i j 1) A=A j j • Matrix.single i i 1 := by
  ext a b
  by_cases ha : i=a <;> by_cases hb : i=b <;>
    simp_all [ad,Matrix.smul_apply]
lemma eraseComplement_apply (i₀ : n) (A : Mat (n⊕e)) :
    eraseComplement i₀ A=A.submatrix Sum.inl Sum.inl+
      (∑ j : e, A (Sum.inr j) (Sum.inr j)) • Matrix.single i₀ i₀ 1 := by
  simp only [eraseComplement,LinearMap.add_apply,LinearMap.sum_apply,ad_apply,
    Matrix.conjTranspose_conjTranspose,coord_compress]
  simp_rw [← ad_apply,single_ad]
  rw [Finset.sum_smul]
lemma eraseComplement_cp (i₀ : n) : CP (eraseComplement (e := e) i₀) := by
  exact cp_add (cp_ad _) (cp_sum _ (fun _ => cp_ad _))
lemma eraseComplement_tp (i₀ : n) : TracePreserving (eraseComplement (e := e) i₀) := by
  intro A
  rw [eraseComplement_apply,Matrix.trace_add,Matrix.trace_smul]
  simp only [Matrix.trace,Matrix.diag,Matrix.submatrix_apply,Fintype.sum_sum_type]
  simp [Matrix.single_apply]
lemma eraseComplement_keep (i₀ : n) (A : Mat n) :
    eraseComplement (e := e) i₀ (ad (coord (Sum.inl : n → n⊕e)) A)=A := by
  rw [eraseComplement_apply]
  have hk := coord_isometry (Sum.inl : n → n⊕e) Sum.inl_injective
  have he : (ad (coord (Sum.inl : n → n⊕e)) A).submatrix Sum.inl Sum.inl=A := by
    rw [← coord_compress,ad_apply]
    simp only [← Matrix.mul_assoc,hk,Matrix.one_mul]
    rw [Matrix.mul_assoc,hk,Matrix.mul_one]
  rw [he]
  have hz (j : e) : ad (coord (Sum.inl : n → n⊕e)) A (Sum.inr j) (Sum.inr j)=0 := by
    simp [ad,coord,Matrix.mul_apply]
  simp only [hz,Finset.sum_const_zero,zero_smul,add_zero]
lemma ad_tracePreserving {a b : Type} [Fintype a] [Fintype b] [DecidableEq a]
    (V : Matrix b a ℂ) (hV : Vᴴ*V=1) : TracePreserving (ad V) := by
  intro A
  rw [ad_apply,Matrix.trace_mul_cycle,hV,Matrix.one_mul]
lemma tp_comp {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    {F : Map a b} {G : Map b c} (hF : TracePreserving F) (hG : TracePreserving G) :
    TracePreserving (G.comp F) := by intro A; exact (hG (F A)).trans (hF A)

theorem finite_purification_recovery (i₀ : n) (B : Matrix e n ℂ) :
    ∃ F : Map e n, CP F ∧ TracePreserving F ∧
      ∀ A : Mat n, F (B*A*Bᴴ)=CFC.sqrt (Bᴴ*B)*A*CFC.sqrt (Bᴴ*B) := by
  let K := coord (Sum.inl : n → n⊕e)
  let J := coord (Sum.inr : e → n⊕e)
  have hK : Kᴴ*K=1 := coord_isometry _ Sum.inl_injective
  have hJ : Jᴴ*J=1 := coord_isometry _ Sum.inr_injective
  let R := Bᴴ*B
  let C := J*B*Kᴴ
  have hgram : Cᴴ*C=K*R*Kᴴ := by
    dsimp [C,R]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ J,hJ,Matrix.one_mul]
  have hsqrt : CFC.sqrt (Cᴴ*C)=K*CFC.sqrt R*Kᴴ := by
    apply CFC.sqrt_unique
    · rw [hgram]
      calc
        (K*CFC.sqrt R*Kᴴ)*(K*CFC.sqrt R*Kᴴ)=K*(CFC.sqrt R*CFC.sqrt R)*Kᴴ := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Kᴴ K,hK,Matrix.one_mul]
        _=K*R*Kᴴ := by rw [CFC.sqrt_mul_sqrt_self R (Matrix.posSemidef_conjTranspose_mul_self B).nonneg]
    · exact ((sqrt_psd R).mul_mul_conjTranspose_same K).nonneg
  obtain ⟨U,hU,hC⟩ := MatrixPolar.polar C
  have hU' := unitary_reverse hU
  have hfactor : Uᴴ*J*B=K*CFC.sqrt R := by
    have hh := congrArg (fun M => Uᴴ*M*K) hC
    rw [hsqrt] at hh
    dsimp only [C] at hh
    simpa only [Matrix.mul_assoc,← Matrix.mul_assoc Kᴴ K,hK,Matrix.mul_one,
      ← Matrix.mul_assoc Uᴴ U,hU,Matrix.one_mul] using hh
  let F := (eraseComplement (e := e) i₀).comp (ad (Uᴴ*J))
  refine ⟨F,cp_comp (eraseComplement_cp i₀) (cp_ad _),?_,?_⟩
  · apply tp_comp _ (eraseComplement_tp i₀)
    apply ad_tracePreserving
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ,hU',Matrix.one_mul,hJ]
  · intro A
    change eraseComplement i₀ (ad (Uᴴ*J) (B*A*Bᴴ))=_
    have hh : ad (Uᴴ*J) (B*A*Bᴴ)=
        ad K (CFC.sqrt R*A*CFC.sqrt R) := by
      have he : (Uᴴ*J)*B=K*CFC.sqrt R := by simpa only [Matrix.mul_assoc] using hfactor
      rw [ad_apply,ad_apply]
      calc
        _=((Uᴴ*J)*B)*A*((Uᴴ*J)*B)ᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
        _=(K*CFC.sqrt R)*A*(K*CFC.sqrt R)ᴴ := by rw [he]
        _=_ := by rw [Matrix.conjTranspose_mul,sqrt_herm]; simp only [Matrix.mul_assoc]
    rw [hh,eraseComplement_keep]

end SecretKey

end

end OAI
