import OAI.InformationTheory.Entanglement.ParityData

namespace OAI

noncomputable section
open scoped BigOperators Kronecker
open Matrix
namespace FiniteConstruction
open ChannelCompletion
lemma ratMatrix_smul (c : ℚ) (A : Matrix Four Four ℚ) :
    (c • A).map (Rat.castHom ℂ)=(c : ℂ) • A.map (Rat.castHom ℂ) := by
  ext i j
  simp
lemma h_real (t : Fin 6) (a : Outcome) (i j : Four) : star (h t a i j)=h t a i j := by
  simp [h]
lemma h_hermitian (t : Fin 6) (a : Outcome) : (h t a).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply,h_real]
  exact congrArg (fun A : Matrix Four Four ℚ => ((A i j : ℚ) : ℂ)) (hQ_symmetric t a)
lemma h_idempotent (t : Fin 6) (a : Outcome) : h t a*h t a=h t a := by
  simpa only [Matrix.map_mul,h] using congrArg (fun A : Matrix Four Four ℚ => A.map (Rat.castHom ℂ)) (hQ_idempotent t a)
lemma h_orthogonal (t : Fin 6) (a b : Outcome) (hab : a ≠ b) : h t a*h t b=0 := by
  unfold h
  rw [← Matrix.map_mul,hQ_orthogonal t a b hab]
  ext i j
  simp
lemma h_complete (t : Fin 6) : ∑ a, h t a=1 := by
  ext i j
  have he := congrArg (fun A : Matrix Four Four ℚ => ((A i j : ℚ) : ℂ)) (hQ_complete t)
  by_cases hij : i=j <;> simpa [h,Matrix.sum_apply,Matrix.one_apply,hij] using he
lemma h_eigen (t : Fin 6) (a : Outcome) (j : Fin 3) :
    context t j*h t a=eigSign t a j • h t a := by
  simpa only [Matrix.map_mul,ratMatrix_smul,h,context,eigSign] using
    congrArg (fun A : Matrix Four Four ℚ => A.map (Rat.castHom ℂ)) (hQ_eigen t a j)
lemma contextQ_symmetric (t : Fin 6) (j : Fin 3) : (contextQ t j)ᵀ=contextQ t j := by
  revert t j
  decide +kernel
lemma context_hermitian (t : Fin 6) (j : Fin 3) : (context t j).IsHermitian := by
  ext i k
  change star ((contextQ t j k i : ℚ) : ℂ)=((contextQ t j i k : ℚ) : ℂ)
  simp only [star_ratCast]
  exact congrArg (fun A : Matrix Four Four ℚ => ((A i k : ℚ) : ℂ)) (contextQ_symmetric t j)
lemma h_eigen_right (t : Fin 6) (a : Outcome) (j : Fin 3) :
    h t a*context t j=eigSign t a j • h t a := by
  have he := congrArg Matrix.conjTranspose (h_eigen t a j)
  simpa only [Matrix.conjTranspose_mul,(h_hermitian t a).eq,(context_hermitian t j).eq,
    Matrix.conjTranspose_smul,eigSign,star_ratCast] using he
lemma shared_context (r c : Fin 3) : context (Fin.castLE (by decide) r) c=
    context ⟨3+c.val,by omega⟩ r := by
  have he : contextQ (Fin.castLE (by decide) r) c = contextQ ⟨3+c.val,by omega⟩ r := by
    revert r c
    decide +kernel
  exact congrArg (fun A : Matrix Four Four ℚ => A.map (Rat.castHom ℂ)) he
lemma eigSignQ_product (t : Fin 6) (a : Outcome) :
    eigSignQ t a 0*eigSignQ t a 1*eigSignQ t a 2=eQ t := by
  revert t a
  decide +kernel
lemma eigSign_product (t : Fin 6) (a : Outcome) :
    eigSign t a 0*eigSign t a 1*eigSign t a 2=(eQ t : ℂ) := by
  unfold eigSign
  exact_mod_cast eigSignQ_product t a

theorem parity_zero_product (a : Fin 6 → Outcome) :
    ∃ t u : Fin 6, t ≠ u ∧ h t (a t)*h u (a u)=0 := by
  by_contra hn
  push Not at hn
  have consistent (r c : Fin 3) :
      eigSign (Fin.castLE (by decide) r) (a (Fin.castLE (by decide) r)) c=
      eigSign ⟨3+c.val,by omega⟩ (a ⟨3+c.val,by omega⟩) r := by
    let t : Fin 6 := Fin.castLE (by decide) r
    let u : Fin 6 := ⟨3+c.val,by omega⟩
    have hne : t ≠ u := by intro he; have := congrArg Fin.val he; dsimp [t,u] at this; omega
    have he : (eigSign t (a t) c-eigSign u (a u) r) • (h t (a t)*h u (a u))=0 := by
      rw [sub_smul,← Matrix.smul_mul,← h_eigen_right,Matrix.mul_assoc,
        shared_context, h_eigen, Matrix.mul_smul,sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp he).resolve_right (hn t u hne))
  have row :
      (eigSign 0 (a 0) 0*eigSign 0 (a 0) 1*eigSign 0 (a 0) 2)*
      (eigSign 1 (a 1) 0*eigSign 1 (a 1) 1*eigSign 1 (a 1) 2)*
      (eigSign 2 (a 2) 0*eigSign 2 (a 2) 1*eigSign 2 (a 2) 2)=1 := by
    rw [eigSign_product,eigSign_product,eigSign_product]
    norm_num [eQ,Fin.ext_iff]
  have col :
      (eigSign 3 (a 3) 0*eigSign 3 (a 3) 1*eigSign 3 (a 3) 2)*
      (eigSign 4 (a 4) 0*eigSign 4 (a 4) 1*eigSign 4 (a 4) 2)*
      (eigSign 5 (a 5) 0*eigSign 5 (a 5) 1*eigSign 5 (a 5) 2)=-1 := by
    rw [eigSign_product,eigSign_product,eigSign_product]
    norm_num [eQ,Fin.ext_iff]
  have hc0 (r : Fin 3) := consistent r 0
  have hc1 (r : Fin 3) := consistent r 1
  have hc2 (r : Fin 3) := consistent r 2
  simp only [show (⟨3+(0:Fin 3).val,by omega⟩ : Fin 6)=3 by rfl] at hc0
  simp only [show (⟨3+(1:Fin 3).val,by omega⟩ : Fin 6)=4 by rfl] at hc1
  simp only [show (⟨3+(2:Fin 3).val,by omega⟩ : Fin 6)=5 by rfl] at hc2
  have h00 := hc0 0
  have h01 := hc1 0
  have h02 := hc2 0
  have h10 := hc0 1
  have h11 := hc1 1
  have h12 := hc2 1
  have h20 := hc0 2
  have h21 := hc1 2
  have h22 := hc2 2
  have ce0 : Fin.castLE (show 3≤6 by decide) (0:Fin 3)=(0:Fin 6) := by decide
  have ce1 : Fin.castLE (show 3≤6 by decide) (1:Fin 3)=(1:Fin 6) := by decide
  have ce2 : Fin.castLE (show 3≤6 by decide) (2:Fin 3)=(2:Fin 6) := by decide
  simp only [ce0,ce1,ce2] at h00 h01 h02 h10 h11 h12 h20 h21 h22
  rw [h00,h01,h02,h10,h11,h12,h20,h21,h22] at row
  have he : (2:ℂ)=0 := by
    linear_combination -row+col
  norm_num at he

end FiniteConstruction

end

end OAI
