import Mathlib
import OAI.Analysis.Commutator.FreeCreation
import OAI.Analysis.Commutator.FreeWordTensor

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma three_block_bound (E P T : H →L[ℂ] H) {a b : ℝ}
    (hE : ‖E‖ ≤ 1)
    (hzero : (1-P)*T*(1-P) = 0)
    (hleft : ‖E*P‖ ≤ a) (hright : ‖P*E‖ ≤ a)
    (hcreate : ‖T*(1-P)‖ ≤ b) (hannihilate : ‖(1-P)*T‖ ≤ b) :
    ‖E*T*E‖ ≤ 2*a*b + a*a*‖T‖ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hleft
  have hb : 0 ≤ b := (norm_nonneg _).trans hcreate
  have hid : E*T*E = (E*P)*(T*(1-P))*E +
      E*((1-P)*T)*(P*E) + (E*P)*T*(P*E) := by
    calc
      E*T*E = (E*P)*(T*(1-P))*E + E*((1-P)*T)*(P*E) +
        (E*P)*T*(P*E) + E*((1-P)*T*(1-P))*E := by noncomm_ring
      _ = _ := by rw [hzero, mul_zero, zero_mul, add_zero]
  have h1 : ‖(E*P)*(T*(1-P))*E‖ ≤ a*b := by
    calc
      _ ≤ ‖E*P‖ * ‖T*(1-P)‖ * ‖E‖ := norm_mul₃_le
      _ ≤ a*b*1 := mul_le_mul
        (mul_le_mul hleft hcreate (norm_nonneg _) ha) hE (norm_nonneg _) (mul_nonneg ha hb)
      _ = _ := mul_one _
  have h2 : ‖E*((1-P)*T)*(P*E)‖ ≤ a*b := by
    calc
      _ ≤ ‖E‖ * ‖(1-P)*T‖ * ‖P*E‖ := norm_mul₃_le
      _ ≤ 1*b*a := mul_le_mul
        (mul_le_mul hE hannihilate (norm_nonneg _) zero_le_one) hright
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 : ‖(E*P)*T*(P*E)‖ ≤ a*a*‖T‖ := by
    calc
      _ ≤ ‖E*P‖ * ‖T‖ * ‖P*E‖ := norm_mul₃_le
      _ ≤ a*‖T‖*a := mul_le_mul
        (mul_le_mul_of_nonneg_right hleft (norm_nonneg _)) hright
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [hid]
  exact (norm_add₃_le).trans (by linarith)

end Kadison.FreeCorner

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

lemma gns_injective : Function.Injective t.functional.gnsStarAlgHom := by
  intro a b hab
  have h := congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS =>
    T (t.functional.toPreGNS 1 : t.functional.GNS)) hab
  have hab' : (t.functional.toPreGNS a : t.functional.GNS) =
      (t.functional.toPreGNS b : t.functional.GNS) := by
    simpa [PositiveLinearMap.gnsStarAlgHom] using h
  exact t.functional.toPreGNS.injective (Completion.coe_injective _ hab')

lemma norm_gns (a : A) : ‖t.functional.gnsStarAlgHom a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (gns_injective t) a

lemma norm_preGNS_projection {e : A} (he : IsStarProjection e) :
    ‖t.functional.toPreGNS e‖ = Real.sqrt (t.functional e).re := by
  rw [t.functional.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, he.isSelfAdjoint.star_eq,
    he.isIdempotentElem.eq]

lemma norm_preGNS_projection_sq {e : A} (he : IsStarProjection e) :
    ‖t.functional.toPreGNS e‖ ^ 2 = (t.functional e).re := by
  have hn := t.functional.preGNS_norm_sq (t.functional.toPreGNS e)
  have h := congrArg Complex.re hn
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, he.isSelfAdjoint.star_eq,
    he.isIdempotentElem.eq, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

include hfree in
lemma one_sub_headProjection (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    1 - (headSpace t S i).starProjection = (tailSpace t S i).starProjection := by
  simp only [headSpace_eq_tailSpace_orthogonal t S hfree i hgen,
    Submodule.starProjection_orthogonal', sub_sub_cancel]

include hfree in
lemma norm_left_headProjection {i j : ι} (hij : i ≠ j) {a : A} (ha : a ∈ S i) :
    ‖t.functional.gnsStarAlgHom a * (headSpace t S j).starProjection‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖t.functional.gnsStarAlgHom a ((headSpace t S j).starProjection x)‖ ≤ _
  rw [norm_mul_tailSpace t S hfree i ha
    (headSpace_le_other_tailSpace t S hij.symm ((headSpace t S j).starProjection_apply_mem x))]
  exact mul_le_mul_of_nonneg_left ((headSpace t S j).norm_starProjection_apply_le x)
    (norm_nonneg _)

include hfree in
lemma norm_right_headProjection {i j : ι} (hij : i ≠ j) {a : A}
    (ha : a ∈ S i) (haStar : IsSelfAdjoint a) :
    ‖(headSpace t S j).starProjection * t.functional.gnsStarAlgHom a‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  have heq : star (t.functional.gnsStarAlgHom a * (headSpace t S j).starProjection) =
      (headSpace t S j).starProjection * t.functional.gnsStarAlgHom a := by
    rw [star_mul, (isSelfAdjoint_starProjection _).star_eq,
      (haStar.map t.functional.gnsStarAlgHom).star_eq]
  rw [← heq, norm_star]
  exact norm_left_headProjection t S hfree hij ha

include hfree in
lemma norm_creation (i : ι) {a : A} (ha : a ∈ S i) :
    ‖t.functional.gnsStarAlgHom a * (tailSpace t S i).starProjection‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖t.functional.gnsStarAlgHom a ((tailSpace t S i).starProjection x)‖ ≤ _
  rw [norm_mul_tailSpace t S hfree i ha ((tailSpace t S i).starProjection_apply_mem x)]
  exact mul_le_mul_of_nonneg_left ((tailSpace t S i).norm_starProjection_apply_le x)
    (norm_nonneg _)

include hfree in
lemma norm_annihilation (i : ι) {a : A} (ha : a ∈ S i) (haStar : IsSelfAdjoint a) :
    ‖(tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  have heq : star (t.functional.gnsStarAlgHom a * (tailSpace t S i).starProjection) =
      (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a := by
    rw [star_mul, (isSelfAdjoint_starProjection _).star_eq,
      (haStar.map t.functional.gnsStarAlgHom).star_eq]
  rw [← heq, norm_star]
  exact norm_creation t S hfree i ha

include hfree in
lemma creation_zero_block (i : ι) {a : A} (ha : a ∈ S i) (ha0 : t.functional a = 0) :
    (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a *
      (tailSpace t S i).starProjection = 0 := by
  ext x
  change (tailSpace t S i).starProjection
    (t.functional.gnsStarAlgHom a ((tailSpace t S i).starProjection x)) = 0
  rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
  apply Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
  apply headSpace_le_tailSpace_orthogonal t S hfree i
  exact creation_mem_headSpace t S i ha ha0 ((tailSpace t S i).starProjection_apply_mem x)

include hfree in
theorem free_compression_norm {i j : ι} (hij : i ≠ j) {e b : A}
    (he : IsStarProjection e) (he_mem : e ∈ S i)
    (hb : IsSelfAdjoint b) (hb_mem : b ∈ S j) (hb0 : t.functional b = 0)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    ‖e*b*e‖ ≤ 2 * Real.sqrt (t.functional e).re * ‖t.functional.toPreGNS b‖ +
      (t.functional e).re * ‖b‖ := by
  let π := t.functional.gnsStarAlgHom
  let P := (headSpace t S j).starProjection
  have hP : 1 - P = (tailSpace t S j).starProjection :=
    one_sub_headProjection t S hfree j hgen
  have h := Kadison.FreeCorner.three_block_bound (π e) P (π b)
    (a := ‖t.functional.toPreGNS e‖) (b := ‖t.functional.toPreGNS b‖)
    ((he.map π).norm_le _) (by rw [hP]; exact creation_zero_block t S hfree j hb_mem hb0)
    (norm_left_headProjection t S hfree hij he_mem)
    (norm_right_headProjection t S hfree hij he_mem he.isSelfAdjoint)
    (by rw [hP]; exact norm_creation t S hfree j hb_mem)
    (by rw [hP]; exact norm_annihilation t S hfree j hb_mem hb)
  have hn : ‖t.functional.toPreGNS e‖ * ‖t.functional.toPreGNS e‖ =
      (t.functional e).re := by simpa only [pow_two] using norm_preGNS_projection_sq t he
  rw [hn, norm_preGNS_projection t he] at h
  simpa only [π, ← map_mul, norm_gns] using h

end Kadison.FreeCreation

namespace Kadison.FreeMoments

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)
  (f : B →⋆ₐ[ℂ] A)

def liftLetter (a : Letter (fun i => (S i).comap f) (τ.comp f.toLinearMap)) : Letter S τ :=
  ⟨a.color,f a.val,a.mem,a.centered⟩

@[simp] lemma liftLetter_color (a) : (liftLetter S τ f a).color=a.color := rfl

@[simp] lemma liftLetter_val (a) : (liftLetter S τ f a).val=f a.val := rfl

lemma word_liftLetter (w : List (Letter (fun i => (S i).comap f) (τ.comp f.toLinearMap))) :
    word (w.map (liftLetter S τ f))=f (word w) := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons,word_cons,liftLetter_val,ih,map_mul]

lemma Free.comap (h : Free S τ) : Free (fun i => (S i).comap f) (τ.comp f.toLinearMap) := by
  intro w hw hne
  have hr : Reduced (w.map (liftLetter S τ f)) := by
    rw [Reduced,List.isChain_map]
    exact hw
  have hz := h (w.map (liftLetter S τ f)) hr (by simpa using hne)
  change τ (f (word w))=0
  rwa [word_liftLetter] at hz

end Kadison.FreeMoments

namespace Kadison.FreeWordTensor

open scoped ComplexOrder

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

def restrictedState : FaithfulState D where
  functional :=
    { toLinearMap := t.functional.toLinearMap.comp f.toLinearMap
      monotone' := fun _ _ hab => t.functional.monotone
        ((NonUnitalStarRingHom.ofClass f).map_le_map_of_map_star hab) }
  normalized := by change t.functional (f 1)=1; simpa using t.normalized
  faithful := by
    intro a ha
    apply hf
    rw [map_zero]
    apply t.faithful
    change t.functional (f (star a*a))=0 at ha
    simpa only [map_mul,map_star] using ha

end Kadison.FreeWordTensor

namespace Kadison.FreeCreation

open FreeWordTensor

open scoped ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

include hfree in
theorem free_compression_norm_intrinsic {i j : ι} (hij : i≠j) {e b : A}
    (he : IsStarProjection e) (he_mem : e∈S i)
    (hb : IsSelfAdjoint b) (hb_mem : b∈S j) (hb0 : t.functional b=0) :
    ‖e*b*e‖ ≤ 2*Real.sqrt (t.functional e).re*‖t.functional.toPreGNS b‖ +
      (t.functional e).re*‖b‖ := by
  let C := (iSup S).topologicalClosure
  let : IsClosed (C : Set A) := StarSubalgebra.isClosed_topologicalClosure _
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let f : C →⋆ₐ[ℂ] A := C.subtype
  let tC := restrictedState t f Subtype.val_injective
  let R : ι → StarSubalgebra ℂ C := fun i => (S i).comap f
  have hR : FreeMoments.Free R tC.functional.toLinearMap := hfree.comap S _ f
  have hinc : iSup S ≤ (iSup R).map f := by
    apply iSup_le
    intro k a ha
    exact ⟨⟨a,StarSubalgebra.le_topologicalClosure _ ((le_iSup S k) ha)⟩,
      (le_iSup R k) ha,rfl⟩
  have hgen : ∀ a : C, tC.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators tC R : Set _)) := by
    let inc : ↥(iSup S) → C := fun x => ⟨x.val,StarSubalgebra.le_topologicalClosure _ x.property⟩
    have hd : DenseRange inc := by
      change DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure (iSup S)))
      apply (denseRange_inclusion_iff _).2
      exact fun _ h => h
    intro a
    apply closure_minimal (s := Set.range inc) ?_
      ((Set.isClosed_centralizer _).preimage
        (AddMonoidHomClass.continuous_of_bound tC.functional.gnsStarAlgHom 1
          (by intro x; simpa using NonUnitalStarAlgHom.norm_apply_le tC.functional.gnsStarAlgHom x))) (hd a)
    rintro _ ⟨x,rfl⟩
    have hm : inc x ∈ iSup R := by
      obtain ⟨y,hy,hxy⟩ := hinc x.property
      have heq : y=inc x := Subtype.ext hxy
      exact heq ▸ hy
    exact Set.subset_centralizer_centralizer ⟨inc x,hm,rfl⟩
  let eC : C := ⟨e,StarSubalgebra.le_topologicalClosure _ ((le_iSup S i) he_mem)⟩
  let bC : C := ⟨b,StarSubalgebra.le_topologicalClosure _ ((le_iSup S j) hb_mem)⟩
  have heC : IsStarProjection eC := ⟨by apply Subtype.ext; exact he.isIdempotentElem,
    by apply Subtype.ext; exact he.isSelfAdjoint⟩
  have hbC : IsSelfAdjoint bC := by apply Subtype.ext; exact hb
  have h := free_compression_norm tC R hR hij heC he_mem hbC hb_mem hb0 hgen
  have hn : ‖tC.functional.toPreGNS bC‖=‖t.functional.toPreGNS b‖ := by
    rw [PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.preGNS_norm_def]
    rfl
  rw [hn] at h
  exact h

end Kadison.FreeCreation

end

end
end

end OAI
