import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.DoubleCoordinates

namespace OAI

section
namespace MarkedSigns

def exponent (h v:ℕ) : ℕ := h*v+h*(h+3)/2
lemma triangular_step (h:ℕ) : (h+1)*(h+1+3)/2 = h*(h+3)/2+h+2 := by
  have he : (h+1)*(h+1+3)=h*(h+3)+2*(h+2) := by ring
  rw [he,Nat.add_mul_div_left]
  all_goals omega
lemma vertical_step (h v:ℕ) : exponent h (v+1)=exponent h v+h := by
  unfold exponent
  ring
lemma horizontal_step (h v:ℕ) : exponent (h+1) v=exponent h v+h+v+2 := by
  unfold exponent
  rw [triangular_step]
  ring
lemma vertical (h v i:ℕ) :
    (-1:ℤ)^h*((-1)^i*(-1)^(exponent h v)) =
      (-1)^(exponent h (v+1)) * (-1)^i := by
  rw [vertical_step,pow_add]
  ring
lemma square (n:ℕ) : (-1:ℤ)^n * (-1)^n=1 := by
  rw [←mul_pow]; norm_num
lemma horizontal (h v j:ℕ) (hj:j≤h+v+2) :
    (-1:ℤ)^j*(-1)^(exponent h v) =
      (-1)^(exponent (h+1) v) * (-1)^(h+v+2-j) := by
  rw [horizontal_step,pow_add,pow_add,pow_add]
  have hs : (-1:ℤ)^(h+v+2)*(-1:ℤ)^(h+v+2-j)=(-1:ℤ)^j := by
    have he:h+v+2=j+(h+v+2-j):=by omega
    rw [he,pow_add]
    have hend : j+(h+v+2-j)-j=h+v+2-j:=by omega
    rw [hend,mul_assoc,square,mul_one]
  have hpow : (-1:ℤ)^h * (-1)^v * (-1)^2=(-1:ℤ)^(h+v+2) := by rw [pow_add,pow_add]
  calc
    _ = (-1:ℤ)^(exponent h v)*((-1:ℤ)^j) := by ring
    _ = (-1:ℤ)^(exponent h v)*((-1:ℤ)^(h+v+2)*(-1:ℤ)^(h+v+2-j)) := by rw [hs]
    _ = _ := by rw [←hpow]; ring
end MarkedSigns

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable abbrev H (p:Skeleton C) : A := (nerve (Fiber p)).homology Z 1
noncomputable def isColimit (n:ℕ) :
    IsColimit (Cofan.mk _ (fun s:Σ_:Fin n,Fin n→Skeleton C => primitive s.2 s.1)) :=
  Cofan.IsColimit.mk _ (fun t=>desc (fun p i=>t.inj ⟨i,p⟩))
    (fun _ s=>primitive_desc _ s.2 s.1)
    (fun t _ hh=>hom_ext (fun p i=>(hh ⟨i,p⟩).trans (primitive_desc (fun p i=>t.inj ⟨i,p⟩) p i).symm))
noncomputable def signIso (h v:ℕ) (M:A) : M≅M where
  hom := (-1:ℤ)^(MarkedSigns.exponent h v) • 𝟙 M
  inv := (-1:ℤ)^(MarkedSigns.exponent h v) • 𝟙 M
  hom_inv_id := by simp only [Preadditive.zsmul_comp,Preadditive.comp_zsmul,Category.id_comp,
    smul_smul,MarkedSigns.square,one_smul]
  inv_hom_id := by simp only [Preadditive.zsmul_comp,Preadditive.comp_zsmul,Category.id_comp,
    smul_smul,MarkedSigns.square,one_smul]
noncomputable def labelIso {n:ℕ} (s:DoubleCoordinates.Index (Skeleton C) n) :
    H s.2.2.1 ≅ H ((DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1) :=
  signIso s.1.val.1 s.1.val.2 _ ≪≫ eqToIso (congrArg H (DoubleCoordinates.center s).symm)
noncomputable def labelDiagramIso (n:ℕ) :
    Discrete.functor (fun s:DoubleCoordinates.Index (Skeleton C) n=>H s.2.2.1) ≅
    Discrete.functor (fun s:DoubleCoordinates.Index (Skeleton C) n=>
      H ((DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1)) :=
  Discrete.natIso (fun s=>labelIso s.as)
noncomputable def reindexedCofan (n:ℕ) := Cofan.mk _
  (fun s:DoubleCoordinates.Index (Skeleton C) n => primitive
    (DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1)
noncomputable def labelledCofan (n:ℕ) := (Cocone.precompose (labelDiagramIso (C:=C) n).hom).obj (reindexedCofan n)
noncomputable def labelledIsColimit (n:ℕ) : IsColimit (labelledCofan (C:=C) n) :=
  (IsColimit.precomposeHomEquiv (labelDiagramIso n) (reindexedCofan n)).symm
    ((Cofan.isColimitEquivOfEquiv (DoubleCoordinates.words (Skeleton C) n) _)
      (isColimit (C:=C) (n+1)))
noncomputable def gradedIso (n:ℕ) :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).X n ≅
      (nerve (IntervalBar.Diagram C (Fin (n+1+1)))).homology Z 1 :=
  (RegularLabels.totalIsColimit (homologyDiagram (C:=C) 1) n).coconePointUniqueUpToIso
    (labelledIsColimit n)
@[reassoc] lemma totalInj_gradedIso {n:ℕ} (s:DoubleCoordinates.Index (Skeleton C) n) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) s ≫ (gradedIso n).hom =
      (labelIso s).hom ≫ primitive (DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1 :=
  (RegularLabels.totalIsColimit (homologyDiagram (C:=C) 1) n).comp_coconePointUniqueUpToIso_hom
    (labelledIsColimit n) ⟨s⟩
end MarkedH1

end

end OAI
