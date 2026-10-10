import Mathlib
import OAI.Analysis.Commutator.FreeBlockTensor3
import OAI.Analysis.Commutator.HankelAlgebra
import OAI.Analysis.Commutator.Regroup
import OAI.Analysis.Commutator.TracialDevelopment

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

abbrev baseEmbedding : multiplicityLevel t S true 0 →ₗᵢ[ℂ] t.functional.GNS :=
  blockEmbedding t S hfree Bool.false_ne_true 0

lemma baseEmbedding_coe (v : factorSpace t S true) :
    baseEmbedding t S hfree (v : multiplicityLevel t S true 0)=
      (t.functional.toPreGNS (factorValue t S true v) : t.functional.GNS) := by
  simp [baseEmbedding,blockEmbedding,blockIsometry,blockReadPre,blockRead]

lemma baseEmbedding_factorOf (a : A) (ha : a∈S true) :
    baseEmbedding t S hfree
      (factorOf t S true a ha : multiplicityLevel t S true 0)=
      (t.functional.toPreGNS a : t.functional.GNS) := by
  rw [baseEmbedding_coe,factorValue_factorOf]

lemma inner_gns_coe (a b : A) :
    inner ℂ (t.functional.toPreGNS a : t.functional.GNS)
      (t.functional.toPreGNS b : t.functional.GNS)=t.functional (star a*b) := by
  rw [Completion.inner_coe]
  rfl

def baseAction (a : A) : multiplicityLevel t S true 0 →L[ℂ] multiplicityLevel t S true 0 :=
  (ContinuousLinearMap.adjoint (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
    (baseEmbedding t S hfree).toContinuousLinearMap).comp
    ((t.functional.gnsStarAlgHom a).comp (baseEmbedding t S hfree).toContinuousLinearMap)

lemma baseAction_inner (a : A) (v z : factorSpace t S true) :
    inner ℂ (z : multiplicityLevel t S true 0)
      (baseAction t S hfree a (v : multiplicityLevel t S true 0))=
      t.functional (star (factorValue t S true z)*a*factorValue t S true v) := by
  dsimp only [baseAction,ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right
    (E := multiplicityLevel t S true 0) (F := t.functional.GNS)]
  change inner ℂ (baseEmbedding t S hfree (z : multiplicityLevel t S true 0))
    (t.functional.gnsStarAlgHom a
      (baseEmbedding t S hfree (v : multiplicityLevel t S true 0)))=_
  rw [baseEmbedding_coe,baseEmbedding_coe,TracialGNS.left_coe,inner_gns_coe,mul_assoc]

lemma base_inner (v z : factorSpace t S true) :
    inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)=
      t.functional (star (factorValue t S true z)*factorValue t S true v) := by
  rw [Completion.inner_coe]
  rfl

def dihedralColumn (e : A) (w : unitary A) (c : ℝ) (n : ℕ) :
    multiplicityLevel t S true 0 →L[ℂ] t.functional.GNS :=
  (c:ℂ) • ((t.functional.gnsStarAlgHom (e*DihedralCorner.wave w (-(n:ℤ)))).comp
    (baseEmbedding t S hfree).toContinuousLinearMap)

lemma dihedralColumn_coe (e : A) (w : unitary A) (c : ℝ) (n : ℕ)
    (v : factorSpace t S true) :
    dihedralColumn t S hfree e w c n (v : multiplicityLevel t S true 0)=
      (c:ℂ) • (t.functional.toPreGNS
        (e*DihedralCorner.wave w (-(n:ℤ))*factorValue t S true v) : t.functional.GNS) := by
  change (c:ℂ) • t.functional.gnsStarAlgHom _
    (baseEmbedding t S hfree (v : multiplicityLevel t S true 0))=_
  rw [baseEmbedding_coe,TracialGNS.left_coe]

lemma dihedralColumn_inner (e h : A) (he : IsStarProjection e) (heh : e*h*e=h)
    (w : unitary A) (c : ℝ) (n m : ℕ) (v z : factorSpace t S true) :
    inner ℂ (dihedralColumn t S hfree e w c n (z : multiplicityLevel t S true 0))
      (t.functional.gnsStarAlgHom h
        (dihedralColumn t S hfree e w c m (v : multiplicityLevel t S true 0)))=
    ((c:ℂ)^2)*t.functional (star (factorValue t S true z)*
      (DihedralCorner.wave w (n:ℤ)*h*DihedralCorner.wave w (-(m:ℤ)))*
      factorValue t S true v) := by
  rw [dihedralColumn_coe,dihedralColumn_coe,map_smul,inner_smul_left,inner_smul_right,
    TracialGNS.left_coe,inner_gns_coe]
  rw [star_mul,star_mul,he.isSelfAdjoint.star_eq,DihedralCorner.wave_star,neg_neg]
  rw [show (starRingEnd ℂ) (c:ℂ)=(c:ℂ) from Complex.conj_ofReal c]
  change (c:ℂ)*((c:ℂ)*t.functional
    (star (factorValue t S true z)*(DihedralCorner.wave w (n:ℤ)*e)*
      (h*(e*DihedralCorner.wave w (-(m:ℤ))*factorValue t S true v))))=_
  rw [←mul_assoc (star (factorValue t S true z))]
  have hm : star (factorValue t S true z)*DihedralCorner.wave w (n:ℤ)*e*
      (h*(e*DihedralCorner.wave w (-(m:ℤ))*factorValue t S true v))=
      star (factorValue t S true z)*
        (DihedralCorner.wave w (n:ℤ)*h*DihedralCorner.wave w (-(m:ℤ)))*
        factorValue t S true v := by
    calc
      _ = star (factorValue t S true z)*
        (DihedralCorner.wave w (n:ℤ)*(e*h*e)*DihedralCorner.wave w (-(m:ℤ)))*
        factorValue t S true v := by simp only [mul_assoc]
      _ = _ := by rw [heh]
  rw [hm,pow_two]
  ring

lemma base_operator_ext
    (T R : multiplicityLevel t S true 0 →L[ℂ] multiplicityLevel t S true 0)
    (h : ∀ v z : factorSpace t S true,
      inner ℂ (z : multiplicityLevel t S true 0) (T (v : multiplicityLevel t S true 0))=
      inner ℂ (z : multiplicityLevel t S true 0) (R (v : multiplicityLevel t S true 0))) : T=R := by
  ext v
  apply ext_inner_left ℂ
  intro z
  induction v,z using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v z => exact h v z

end Kadison.FreeBlocks

end

end
end

end OAI
