import OAI.Combinatorics.HoneycombChords.FunctionalTransforms
import OAI.Combinatorics.HoneycombChords.OrderedDeterminants

namespace OAI

/-! Bilinear Gram projection onto the finite interpolation space and its residuals.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional
open Finset
open StripAsymptotic

noncomputable def complexInsertedFamily (N : ℕ) (H : ℝ → ℂ) : Fin (2*N+1) → ℝ → ℂ :=
  Function.update (fun i x => (fixedFamily N i x : ℂ)) (centralIndex N) H

lemma complexInsertedFamily_low (N : ℕ) (H : ℝ → ℂ) (k : Fin N) :
    complexInsertedFamily N H ⟨k,by omega⟩ = fun x => (cosineKernelJet k 0 0 x : ℂ) := by
  have hi : (⟨k,by omega⟩ : Fin (2*N+1)) ≠ centralIndex N := by
    simp only [ne_eq,Fin.ext_iff,centralIndex]
    exact Nat.ne_of_lt k.isLt
  ext x
  rw [complexInsertedFamily,Function.update_of_ne hi]
  rw [fixedFamily,interiorKnot_nodalOrder N _ (half_pos strip_angle_pos) (by linarith [strip_angle_pos])]
  simp [interiorKnotLabels,k.isLt]

lemma complexInsertedFamily_high (N : ℕ) (H : ℝ → ℂ) (k : Fin N) :
    complexInsertedFamily N H ⟨N+1+k,by omega⟩ = fun x => (cosineKernelJet k 0 (angle^2) x : ℂ) := by
  have hi : (⟨N+1+k,by omega⟩ : Fin (2*N+1)) ≠ centralIndex N := by
    simp only [ne_eq,Fin.ext_iff,centralIndex]
    omega
  have hlt : ¬N+1+(k:ℕ)<N := by omega
  have hne : N+1+(k:ℕ) ≠ N := by omega
  ext x
  rw [complexInsertedFamily,Function.update_of_ne hi]
  rw [fixedFamily,interiorKnot_nodalOrder N _ (half_pos strip_angle_pos) (by linarith [strip_angle_pos])]
  simp [interiorKnotLabels,hlt,hne]

lemma beta_angle_mem_M (N : ℕ) (k : Fin N) :
    (fun x => (cosineKernelJet k 0 (angle^2) x : ℂ)) ∈ M N := by
  have h : (fun x => (cosineKernelJet k 0 (angle^2) x : ℂ)) ∈
      Submodule.span ℂ ((fun j : ℕ => fun x : ℝ => (cosineKernelJet j 0 (angle^2) x : ℂ)) '' Set.Iio N) :=
    Submodule.subset_span ⟨k,k.isLt,rfl⟩
  rw [parameter_jet_span angle strip_angle_pos.ne' N] at h
  apply (Submodule.span_mono (show ((fun j : ℕ=>fun x : ℝ=>iteratedDeriv j (fun t=>C t x) angle) '' Set.Iio N) ⊆
      Set.range (fun j : Fin N => fun x : ℝ => (x:ℂ)^j.val) ∪
      Set.range (fun j : Fin N => fun x : ℝ => iteratedDeriv j.val (fun t=>C t x) angle) from ?_)) h
  rintro _ ⟨j,hj,rfl⟩
  exact Or.inr ⟨⟨j,hj⟩,rfl⟩

lemma beta_zero_mem_M (N : ℕ) (k : Fin N) :
    (fun x => (cosineKernelJet k 0 0 x : ℂ)) ∈ M N := by
  have h : (fun x : ℝ => (x:ℂ)^k.val) ∈ M N := Submodule.subset_span (Or.inl ⟨k,rfl⟩)
  have he : (fun x => (cosineKernelJet k 0 0 x : ℂ)) =
      (((2*(k:ℕ)).factorial:ℂ)⁻¹) • (fun x : ℝ => (x:ℂ)^k.val) := by
    ext x
    simp [cosineKernelJet_at_zero,div_eq_mul_inv,mul_comm]
  rw [he]
  exact (M N).smul_mem _ h

lemma complexInsertedFamily_span (N : ℕ) (H : ℝ → ℂ) :
    Submodule.span ℂ (Set.range (complexInsertedFamily N H)) = M N ⊔ Submodule.span ℂ {H} := by
  let S := Submodule.span ℂ (Set.range (complexInsertedFamily N H))
  have hlow (k : Fin N) : (fun x => (cosineKernelJet k 0 0 x : ℂ)) ∈ S := by
    rw [← complexInsertedFamily_low N H k]
    exact Submodule.subset_span ⟨_,rfl⟩
  have hhigh (k : Fin N) : (fun x => (cosineKernelJet k 0 (angle^2) x : ℂ)) ∈ S := by
    rw [← complexInsertedFamily_high N H k]
    exact Submodule.subset_span ⟨_,rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hic : i=centralIndex N
    · subst i
      simp only [complexInsertedFamily,Function.update_self]
      exact (show Submodule.span ℂ {H} ≤ M N ⊔ Submodule.span ℂ {H} from le_sup_right) (Submodule.subset_span (Set.mem_singleton H))
    · by_cases hil : (i:ℕ)<N
      · have he : i=⟨(⟨i,hil⟩:Fin N),by omega⟩ := rfl
        rw [he,complexInsertedFamily_low]
        exact (show M N ≤ M N ⊔ Submodule.span ℂ {H} from le_sup_left) (beta_zero_mem_M N ⟨i,hil⟩)
      · have hne : (i:ℕ)≠N := by simpa [Fin.ext_iff,centralIndex] using hic
        have hk : (i:ℕ)-(N+1)<N := by omega
        have he : i=⟨N+1+(⟨(i:ℕ)-(N+1),hk⟩:Fin N),by omega⟩ := by apply Fin.ext; dsimp;omega
        rw [he,complexInsertedFamily_high]
        exact (show M N ≤ M N ⊔ Submodule.span ℂ {H} from le_sup_left) (beta_angle_mem_M N ⟨(i:ℕ)-(N+1),hk⟩)
  · apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ (⟨k,rfl⟩|⟨k,rfl⟩)
      · have he : (fun x : ℝ=>(x:ℂ)^k.val)=((2*(k:ℕ)).factorial:ℂ) •
            (fun x => (cosineKernelJet k 0 0 x : ℂ)) := by
          ext x
          simp only [Pi.smul_apply,smul_eq_mul,cosineKernelJet_at_zero,Complex.ofReal_div,
            Complex.ofReal_pow,Complex.ofReal_natCast]
          have hfac : (((2*(k:ℕ)).factorial:ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          field_simp
        change (fun x : ℝ => (x:ℂ)^k.val) ∈ S
        rw [he]
        exact S.smul_mem _ (hlow k)
      · have hspan : Submodule.span ℂ ((fun j : ℕ=>fun x : ℝ=>(cosineKernelJet j 0 (angle^2) x:ℂ)) '' Set.Iio N) ≤ S := by
          apply Submodule.span_le.mpr
          rintro _ ⟨j,hj,rfl⟩
          exact hhigh ⟨j,hj⟩
        rw [parameter_jet_span angle strip_angle_pos.ne' N] at hspan
        exact hspan (Submodule.subset_span ⟨k,k.isLt,rfl⟩)
    · apply Submodule.span_le.mpr
      intro f hf
      have : f=H := Set.mem_singleton_iff.mp hf
      subst f
      have he : complexInsertedFamily N H (centralIndex N)=H := Function.update_self _ _ _
      exact Submodule.subset_span ⟨centralIndex N,he⟩

lemma fixedFamily_span (N : ℕ) :
    Submodule.span ℂ (Set.range (fun i x => (fixedFamily N i x : ℂ))) =
      M N ⊔ Submodule.span ℂ {C (angle/2)} := by
  have he : complexInsertedFamily N (C (angle/2)) = fun i x=>(fixedFamily N i x:ℂ) := by
    unfold complexInsertedFamily
    apply Function.update_eq_self_iff.mpr
    ext x
    rw [fixedFamily_central,C_eq_beta_square]
  rw [←he]
  exact complexInsertedFamily_span _ _

lemma mixedFamily_span (N : ℕ) :
    Submodule.span ℂ (Set.range (fun i x => (mixedFamily N i x : ℂ))) = admissibleDensity N := by
  have he : complexInsertedFamily N g = fun i x=>(mixedFamily N i x:ℂ) := by
    ext i x
    by_cases hi : i=centralIndex N
    · subst i
      simp only [complexInsertedFamily,mixedFamily,Function.update_self,realG_complex]
    · simp only [complexInsertedFamily,mixedFamily,Function.update_of_ne hi]
  rw [←he,complexInsertedFamily_span]
  rfl

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Finset MeasureTheory

lemma pairing_sub {H K F : ℝ → ℂ} (hH : PairingIntegrable H F)
    (hK : PairingIntegrable K F) : pairing (H-K) F=pairing H F-pairing K F := by
  unfold pairing
  have he : (fun z : ℝ => (H-K) (z^2)*F (z^2)*((z:ℂ)*D (z^2)/(Real.sinh (4*angle*z):ℂ))) =
      pairingKernel H F - pairingKernel K F := by ext z; simp [pairingKernel];ring
  rw [he]
  exact integral_sub hH hK

lemma pairing_add {H K F : ℝ → ℂ} (hH : PairingIntegrable H F)
    (hK : PairingIntegrable K F) : pairing (H+K) F=pairing H F+pairing K F := by
  change (∫ z in Set.Ioi (0:ℝ),pairingKernel (H+K) F z)=_
  rw [pairingKernel_add]
  exact integral_add hH hK

lemma pairing_smul (a : ℂ) (H F : ℝ → ℂ) : pairing (a • H) F = a*pairing H F := by
  change (∫ z in Set.Ioi (0:ℝ),pairingKernel (a • H) F z)=_
  rw [pairingKernel_smul]
  exact integral_const_mul _ _

lemma pairing_comm (H F : ℝ → ℂ) : pairing H F=pairing F H := by
  unfold pairing
  congr 1
  ext z
  ring

lemma PairingIntegrable.comm {H F : ℝ → ℂ} (h : PairingIntegrable H F) : PairingIntegrable F H := by
  have he : pairingKernel F H=pairingKernel H F := by ext z; dsimp [pairingKernel];ring
  unfold PairingIntegrable at *
  rw [he]
  exact h

lemma PairingIntegrable.sub {H K F : ℝ → ℂ} (hH : PairingIntegrable H F)
    (hK : PairingIntegrable K F) : PairingIntegrable (H-K) F := by
  simpa only [sub_eq_add_neg,neg_one_smul] using hH.add (hK.smul (-1))

lemma PairingIntegrable.finset_sum {ι : Type*} (s : Finset ι) (H : ι → ℝ → ℂ) (F : ℝ → ℂ)
    (hi : ∀ i ∈ s,PairingIntegrable (H i) F) : PairingIntegrable (∑ i ∈ s,H i) F := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty] using PairingIntegrable.zero F
  | @insert a s ha ih =>
    rw [sum_insert ha]
    exact (hi a (mem_insert_self _ _)).add (ih (fun i hi'=>hi i (mem_insert_of_mem hi')))

lemma pairing_finset_sum {ι : Type*} (s : Finset ι) (H : ι → ℝ → ℂ) (F : ℝ → ℂ)
    (hi : ∀ i ∈ s,PairingIntegrable (H i) F) : pairing (∑ i ∈ s,H i) F=∑ i ∈ s,pairing (H i) F := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairing]
  | @insert a s ha ih =>
    rw [sum_insert ha,sum_insert ha,pairing_add (hi a (mem_insert_self _ _))
      (PairingIntegrable.finset_sum s H F (fun i hi'=>hi i (mem_insert_of_mem hi'))),
      ih (fun i hi'=>hi i (mem_insert_of_mem hi'))]

lemma PairingIntegrable.span_left {S : Set (ℝ → ℂ)} {F : ℝ → ℂ}
    (hi : ∀ H ∈ S,PairingIntegrable H F) {H : ℝ → ℂ} (hH : H ∈ Submodule.span ℂ S) :
    PairingIntegrable H F := by
  induction hH using Submodule.span_induction with
  | mem H hH => exact hi H hH
  | zero => exact PairingIntegrable.zero F
  | add H K hH hK hiH hiK => exact hiH.add hiK
  | smul a H hH hiH => exact hiH.smul a

lemma pairing_annihilates_span {S : Set (ℝ → ℂ)} {H : ℝ → ℂ}
    (hi : ∀ F ∈ S,PairingIntegrable H F) (hz : ∀ F ∈ S,pairing H F=0)
    {F : ℝ → ℂ} (hF : F ∈ Submodule.span ℂ S) : pairing H F=0 := by
  induction hF using Submodule.span_induction with
  | mem F hF => exact hz F hF
  | zero => simp [pairing]
  | add F K hF hK hiF hiK =>
    rw [pairing_comm,pairing_add (PairingIntegrable.span_left (fun F hF=>(hi F hF).comm) hF)
      (PairingIntegrable.span_left (fun F hF=>(hi F hF).comm) hK),pairing_comm F H,pairing_comm K H,hiF,hiK,add_zero]
  | smul a F hF hiF => rw [pairing_comm,pairing_smul,pairing_comm F H,hiF,mul_zero]

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Finset Matrix MeasureTheory
open StripAsymptotic
noncomputable def fBasis (N : ℕ) (i : Fin (2*N+1)) (x : ℝ) : ℂ := fixedFamily N i x
noncomputable def gBasis (N : ℕ) (i : Fin (2*N+1)) (x : ℝ) : ℂ := mixedFamily N i x
noncomputable def pairingMatrix (N : ℕ) : Matrix (Fin (2*N+1)) (Fin (2*N+1)) ℂ :=
  Matrix.of (fun j i=>pairing (fBasis N i) (gBasis N j))

lemma pairingKernel_ofReal (H F : ℝ → ℝ) {p : ℝ} (hp : 0≤p) :
    pairingKernel (fun x=>(H x:ℂ)) (fun x=>(F x:ℂ)) p =
      ((H (p^2)*F (p^2)*stripDensity p:ℝ):ℂ) := by
  rw [pairingKernel,D_sq hp]
  simp only [stripDensity,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_ofNat,
    Complex.ofReal_one,Complex.ofReal_div]

lemma pairing_ofReal (H F : ℝ → ℝ) :
    pairing (fun x=>(H x:ℂ)) (fun x=>(F x:ℂ)) =
      ((∫ p in Set.Ioi (0:ℝ),H (p^2)*F (p^2)*stripDensity p:ℝ):ℂ) := by
  change (∫ p in Set.Ioi (0:ℝ),pairingKernel (fun x=>(H x:ℂ)) (fun x=>(F x:ℂ)) p)=_
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact pairingKernel_ofReal H F hp.le

lemma fBasis_gBasis_integrable (N : ℕ) (i j : Fin (2*N+1)) :
    PairingIntegrable (fBasis N i) (gBasis N j) := by
  have hi : IntegrableOn (fun p=>((fixedFamily N i (p^2)*mixedFamily N j (p^2)*stripDensity p:ℝ):ℂ)) (Set.Ioi 0) :=
    (fixed_mixed_pair_integrable N i j).ofReal
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  exact (pairingKernel_ofReal (fixedFamily N i) (mixedFamily N j) hp.le).symm

lemma pairingMatrix_eq (N : ℕ) :
    pairingMatrix N = ((familyGram stripDensity (fixedFamily N) (mixedFamily N)).map Complex.ofReal).transpose := by
  ext j i
  exact pairing_ofReal _ _

lemma pairingMatrix_det_ne_zero (N : ℕ) : (pairingMatrix N).det ≠ 0 := by
  rw [pairingMatrix_eq,Matrix.det_transpose]
  change (Complex.ofRealHom.mapMatrix (familyGram stripDensity (fixedFamily N) (mixedFamily N))).det ≠ 0
  rw [← RingHom.map_det Complex.ofRealHom]
  exact Complex.ofReal_ne_zero.mpr (fixed_mixed_Gram_det_pos N).ne'

lemma fBasis_span (N : ℕ) : Submodule.span ℂ (Set.range (fBasis N)) =
    M N ⊔ Submodule.span ℂ {C (angle/2)} := fixedFamily_span N
lemma gBasis_span (N : ℕ) : Submodule.span ℂ (Set.range (gBasis N)) =
    admissibleDensity N := mixedFamily_span N

lemma fBasis_density_integrable {N : ℕ} {F : ℝ → ℂ} (hF : F ∈ admissibleDensity N)
    (i : Fin (2*N+1)) : PairingIntegrable (fBasis N i) F := by
  rw [← gBasis_span] at hF
  apply PairingIntegrable.comm
  apply PairingIntegrable.span_left (S:=Set.range (gBasis N)) _ hF
  rintro _ ⟨j,rfl⟩
  exact (fBasis_gBasis_integrable N i j).comm

end CriticalHoneycomb.FiniteFunctional

end


section


namespace CriticalHoneycomb.FiniteFunctional
open Finset Matrix MeasureTheory

noncomputable def projectionCoefficients (N : ℕ) (H : ℝ → ℂ) : Fin (2*N+1) → ℂ :=
  (pairingMatrix N)⁻¹ *ᵥ (fun j=>pairing H (gBasis N j))
noncomputable def obliqueProjection (N : ℕ) (H : ℝ → ℂ) : ℝ → ℂ :=
  ∑ i,projectionCoefficients N H i • fBasis N i
noncomputable def obliqueResidual (N : ℕ) (H : ℝ → ℂ) : ℝ → ℂ := H-obliqueProjection N H

def InPairingDomain (N : ℕ) (H : ℝ → ℂ) : Prop := ∀ j,PairingIntegrable H (gBasis N j)

lemma projection_mem (N : ℕ) (H : ℝ → ℂ) :
    obliqueProjection N H ∈ M N ⊔ Submodule.span ℂ {C (angle/2)} := by
  rw [← fBasis_span]
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨projectionCoefficients N H,rfl⟩

lemma projection_integrable (N : ℕ) (H : ℝ → ℂ) (j : Fin (2*N+1)) :
    PairingIntegrable (obliqueProjection N H) (gBasis N j) := by
  apply PairingIntegrable.finset_sum
  intro i _
  exact (fBasis_gBasis_integrable N i j).smul _

lemma projection_pairing (N : ℕ) (H : ℝ → ℂ) (j : Fin (2*N+1)) :
    pairing (obliqueProjection N H) (gBasis N j)=pairing H (gBasis N j) := by
  rw [obliqueProjection,pairing_finset_sum _ _ _ (fun i _=>(fBasis_gBasis_integrable N i j).smul _)]
  simp_rw [pairing_smul]
  have h := congrFun (show (pairingMatrix N) *ᵥ projectionCoefficients N H=
      (fun j=>pairing H (gBasis N j)) from by
        rw [projectionCoefficients,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr (pairingMatrix_det_ne_zero N)),Matrix.one_mulVec]) j
  simpa only [Matrix.mulVec, dotProduct, pairingMatrix,Matrix.of_apply,mul_comm] using h

lemma residual_pairing_zero {N : ℕ} {H : ℝ → ℂ} (hH : InPairingDomain N H) (j : Fin (2*N+1)) :
    pairing (obliqueResidual N H) (gBasis N j)=0 := by
  rw [obliqueResidual,pairing_sub (hH j) (projection_integrable N H j),projection_pairing,sub_self]

lemma residual_density_pairing_zero {N : ℕ} {H F : ℝ → ℂ} (hH : InPairingDomain N H)
    (hF : F ∈ admissibleDensity N) : pairing (obliqueResidual N H) F=0 := by
  rw [← gBasis_span] at hF
  apply pairing_annihilates_span (S:=Set.range (gBasis N)) _ _ hF
  · rintro _ ⟨j,rfl⟩
    exact (hH j).sub (projection_integrable N H j)
  · rintro _ ⟨j,rfl⟩
    exact residual_pairing_zero hH j

lemma domain_density_integrable {N : ℕ} {H F : ℝ → ℂ} (hH : InPairingDomain N H)
    (hF : F ∈ admissibleDensity N) : PairingIntegrable H F := by
  rw [← gBasis_span] at hF
  apply PairingIntegrable.comm
  apply PairingIntegrable.span_left (S:=Set.range (gBasis N)) _ hF
  rintro _ ⟨j,rfl⟩
  exact (hH j).comm

lemma projection_density_integrable {N : ℕ} {F : ℝ → ℂ} (H : ℝ → ℂ)
    (hF : F ∈ admissibleDensity N) : PairingIntegrable (obliqueProjection N H) F :=
  domain_density_integrable (projection_integrable N H) hF

lemma projection_unique {N : ℕ} {H P : ℝ → ℂ}
    (hP : P ∈ M N ⊔ Submodule.span ℂ {C (angle/2)})
    (hp : ∀ j,pairing P (gBasis N j)=pairing H (gBasis N j)) : P=obliqueProjection N H := by
  rw [← fBasis_span] at hP
  obtain ⟨v,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hP
  have hv : (pairingMatrix N) *ᵥ v=(pairingMatrix N) *ᵥ projectionCoefficients N H := by
    ext j
    have he (u : Fin (2*N+1)→ℂ) :
        pairing (∑ i,u i • fBasis N i) (gBasis N j)=((pairingMatrix N)*ᵥ u) j := by
      rw [pairing_finset_sum _ _ _ (fun i _=>(fBasis_gBasis_integrable N i j).smul _)]
      simp only [pairing_smul,pairingMatrix,Matrix.mulVec,dotProduct,Matrix.of_apply,mul_comm]
    rw [←he v,←he (projectionCoefficients N H),hp j]
    exact (projection_pairing N H j).symm
  have hv' : v=projectionCoefficients N H :=
    (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (pairingMatrix_det_ne_zero N)))) hv
  rw [hv']
  rfl

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional
open Finset Matrix MeasureTheory
open StripAsymptotic

lemma real_projection_coefficients (N : ℕ) (H : ℝ → ℝ) :
    projectionCoefficients N (fun x=>(H x:ℂ))=
      fun i=>(((familyGram stripDensity (fixedFamily N) (mixedFamily N)).transpose⁻¹ *ᵥ
        (fun j=>∫ p in Set.Ioi 0,H (p^2)*mixedFamily N j (p^2)*stripDensity p)) i:ℂ) := by
  let A:=familyGram stripDensity (fixedFamily N) (mixedFamily N)
  let v:=fun j=>∫ p in Set.Ioi 0,H (p^2)*mixedFamily N j (p^2)*stripDensity p
  let c:=A.transpose⁻¹ *ᵥ v
  have hd : IsUnit A.transpose.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr (fixed_mixed_Gram_det_pos N).ne'
  have hc : A.transpose *ᵥ c=v := by
    change A.transpose *ᵥ (A.transpose⁻¹ *ᵥ v)=v
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hd,Matrix.one_mulVec]
  have hcx : pairingMatrix N *ᵥ (fun i=>(c i:ℂ))=
      fun j=>pairing (fun x=>(H x:ℂ)) (gBasis N j) := by
    ext j
    rw [pairingMatrix_eq]
    change (∑ i,(A i j:ℂ)*(c i:ℂ))=pairing (fun x=>(H x:ℂ)) (fun x=>(mixedFamily N j x:ℂ))
    rw [pairing_ofReal]
    norm_cast
    exact congrFun hc j
  have hsol : projectionCoefficients N (fun x=>(H x:ℂ))=fun i=>(c i:ℂ) := by
    rw [projectionCoefficients,←hcx,Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (pairingMatrix_det_ne_zero N)),Matrix.one_mulVec]
  exact hsol

lemma projection_ofReal (N : ℕ) (H : ℝ → ℝ) (a : ℝ) :
    obliqueProjection N (fun x=>(H x:ℂ)) a=
      (((fun j=>∫ p in Set.Ioi 0,H (p^2)*mixedFamily N j (p^2)*stripDensity p) ⬝ᵥ
        ((familyGram stripDensity (fixedFamily N) (mixedFamily N))⁻¹ *ᵥ
          (fun i=>fixedFamily N i a))):ℝ) := by
  rw [obliqueProjection,real_projection_coefficients]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,fBasis]
  simp_rw [←Complex.ofReal_mul]
  rw [←Complex.ofReal_sum]
  congr 1
  rw [Matrix.dotProduct_mulVec,←Matrix.transpose_nonsing_inv]
  simp only [dotProduct,Matrix.vecMul,Matrix.mulVec,Matrix.transpose_apply,mul_comm]

lemma residual_ofReal_mean (N : ℕ) (H : ℝ → ℝ) {a : ℝ} (ha : H a≠0)
    (hH : ∀ j,IntegrableOn (fun p=>H (p^2)*mixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0)) :
    obliqueResidual N (fun x=>(H x:ℂ)) a=
      ((H a*meanResidualRatio stripDensity (fixedFamily N) (mixedFamily N) H a:ℝ):ℂ) := by
  rw [obliqueResidual,Pi.sub_apply,projection_ofReal,←Complex.ofReal_sub]
  congr 1
  rw [meanResidualRatio_formula _ _ _ _ _ (fixed_mixed_pair_integrable N) hH
    (fixed_mixed_Gram_det_pos N).ne']
  have he : (fun i : Fin (2*N+1)=>fixedFamily N i a/H a)=(H a)⁻¹ • (fun i=>fixedFamily N i a) := by
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mulVec_smul,dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology

lemma cosh_parameter_norm {p t : ℝ} (hp : 0 ≤ p) (ht : t ∈ Set.Icc (0:ℝ) angle) :
    |Real.cosh (t*p)| ≤ Real.cosh (angle*p) := by
  rw [abs_of_pos (Real.cosh_pos _)]
  apply Real.cosh_le_cosh.mpr
  rw [abs_of_nonneg (mul_nonneg ht.1 hp),abs_of_nonneg (mul_nonneg strip_angle_pos.le hp)]
  exact mul_le_mul_of_nonneg_right ht.2 hp

lemma cosh_pair_continuousOn (q : ℝ → ℝ) (hq : Measurable q)
    (hi : IntegrableOn (fun p=>|q p| *Real.cosh (angle*p)) (Set.Ioi 0)) :
    ContinuousOn (fun t=>∫ p in Set.Ioi 0,q p*Real.cosh (t*p)) (Set.Icc 0 angle) := by
  apply continuousOn_of_dominated (bound:=fun p=>|q p| *Real.cosh (angle*p))
  · intro t ht
    exact (hq.mul (by fun_prop)).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    rw [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_left (cosh_parameter_norm hp.le ht) (abs_nonneg _)
  · exact hi
  · filter_upwards with p
    exact (show Continuous (fun t=>q p*Real.cosh (t*p)) by fun_prop).continuousOn

lemma cosh_pair_fubini (q : ℝ → ℝ) (hq : Measurable q)
    (hi : IntegrableOn (fun p=>|q p| *Real.cosh (angle*p)) (Set.Ioi 0)) :
    (∫ p in Set.Ioi 0,q p*realG (p^2)) =
      ∫ t in (0:ℝ)..angle,∫ p in Set.Ioi 0,q p*Real.cosh (t*p) := by
  let μ:=volume.restrict (Set.Ioc (0:ℝ) angle)
  let ν:=volume.restrict (Set.Ioi (0:ℝ))
  have hprod : Integrable (fun z : ℝ × ℝ=>q z.2*Real.cosh (z.1*z.2)) (μ.prod ν) := by
    apply (hi.comp_snd μ).mono'
    · exact ((hq.comp measurable_snd).mul (by fun_prop)).aestronglyMeasurable
    · have ht : ∀ᵐ z : ℝ × ℝ ∂μ.prod ν,z.1 ∈ Set.Ioc (0:ℝ) angle :=
        (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc))
      have hp : ∀ᵐ z : ℝ × ℝ ∂μ.prod ν,0<z.2 :=
        (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi))
      filter_upwards [ht,hp] with z ht hp
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (cosh_parameter_norm hp.le ⟨ht.1.le,ht.2⟩) (abs_nonneg _)
  rw [intervalIntegral.integral_of_le strip_angle_pos.le]
  rw [integral_integral_swap hprod]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  rw [integral_const_mul,←intervalIntegral.integral_of_le strip_angle_pos.le]
  congr 1
  unfold realG
  apply intervalIntegral.integral_congr
  intro t ht
  apply Complex.ofReal_injective
  rw [←C_eq_beta_square,C_sq _ hp.le]

lemma colDet_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (v : ℝ → Fin n → ℝ) {a b : ℝ} (hv : IntervalIntegrable v volume a b) :
    (A.updateCol i (fun j=>∫ t in a..b,v t j)).det =
      ∫ t in a..b,(A.updateCol i (v t)).det := by
  let L := (rowDetLinear A.transpose i).toContinuousLinearMap
  have he : (∫ t in a..b,v t)=fun j=>∫ t in a..b,v t j := by
    funext j
    exact ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm hv).symm
  have h:=L.intervalIntegral_comp_comm hv
  rw [he] at h
  have htrans (w : Fin n → ℝ) : (A.transpose.updateRow i w).det=(A.updateCol i w).det := by
    rw [←Matrix.det_transpose (A.updateCol i w)]
    congr 1
    ext k j
    simp [Matrix.updateRow_apply,Matrix.updateCol_apply]
  change (∫ t in a..b,(A.transpose.updateRow i (v t)).det)=
    (A.transpose.updateRow i (fun j=>∫ t in a..b,v t j)).det at h
  simpa only [htrans] using h.symm

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
