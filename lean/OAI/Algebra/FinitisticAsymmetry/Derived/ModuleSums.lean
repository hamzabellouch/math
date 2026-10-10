import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v
open HomologicalComplex
variable {R : Type u} [Ring R] {I : Type v}

def moduleSumCofan (X : I → ModuleCat.{max u v} R) : Cofan X := by
  classical
  exact Cofan.mk (ModuleCat.of R (Π₀ i, X i)) (fun i => ModuleCat.ofHom (DFinsupp.lsingle (R := R) (M := fun j => X j) i))

def moduleSumIsColimit (X : I → ModuleCat.{max u v} R) :
    IsColimit (moduleSumCofan X) := by
  classical
  refine Cofan.IsColimit.mk _ (fun s => ModuleCat.ofHom (DFinsupp.lsum ℤ
    (fun i => (s.inj i).hom))) ?_ ?_
  · intro s i
    ext x
    change DFinsupp.lsum ℤ (fun j => (s.inj j).hom) (DFinsupp.single i x) = _
    simp only [DFinsupp.lsum_single]
  · intro s m hm
    apply ModuleCat.hom_ext
    apply DFinsupp.lhom_ext
    intro i x
    change m (DFinsupp.single i x) = DFinsupp.lsum ℤ (fun j => (s.inj j).hom) (DFinsupp.single i x)
    rw [DFinsupp.lsum_single]
    exact ConcreteCategory.congr_hom (hm i) x

def moduleSumComplex (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) :
    CochainComplex (ModuleCat R) ℤ where
  X j := ModuleCat.of R (Π₀ i, (K i).X j)
  d j k := ModuleCat.ofHom (DFinsupp.mapRange.linearMap (fun i => ((K i).d j k).hom))
  shape j k hjk := by
    ext x i
    change (K i).d j k (x i) = 0
    rw [(K i).shape j k hjk]
    rfl
  d_comp_d' j k l hjk hkl := by
    ext x i
    change ((K i).d k l) (((K i).d j k) (x i)) = 0
    exact ConcreteCategory.congr_hom ((K i).d_comp_d j k l) (x i)

def moduleSumComplexInj (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) (i : I) :
    K i ⟶ moduleSumComplex K := by
  classical
  refine { f := fun j => ModuleCat.ofHom (DFinsupp.lsingle (R := R)
      (M := fun n => (K n).X j) i), comm' := ?_ }
  intro j k hjk
  ext x
  change DFinsupp.mapRange (fun i => ((K i).d j k).hom) (fun i => map_zero _) (DFinsupp.single i x) =
    DFinsupp.single i ((K i).d j k x)
  rw [DFinsupp.mapRange_single]

def moduleSumComplexCofan (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) : Cofan K :=
  Cofan.mk _ (moduleSumComplexInj K)

def moduleSumComplexIsColimit (K : I → CochainComplex (ModuleCat.{max u v} R) ℤ) :
    IsColimit (moduleSumComplexCofan K) := by
  classical
  refine Cofan.IsColimit.mk _ (fun s =>
    { f := fun j => ModuleCat.ofHom (DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom))
      comm' := ?_ }) ?_ ?_
  · intro j k hjk
    apply ModuleCat.hom_ext
    apply DFinsupp.lhom_ext
    intro i x
    change s.pt.d j k (DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom)
        (DFinsupp.single i x)) =
      DFinsupp.lsum ℤ (fun i => ((s.inj i).f k).hom)
        (DFinsupp.mapRange (fun i => ((K i).d j k).hom) (fun i => map_zero _) (DFinsupp.single i x))
    simp only [DFinsupp.mapRange_single, DFinsupp.lsum_single]
    exact ConcreteCategory.congr_hom ((s.inj i).comm j k) x
  · intro s i
    ext j x
    change DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom) (DFinsupp.single i x) = _
    simp only [DFinsupp.lsum_single]
  · intro s m hm
    apply HomologicalComplex.Hom.ext
    funext j
    apply ModuleCat.hom_ext
    apply DFinsupp.lhom_ext
    intro i x
    change m.f j (DFinsupp.single i x) =
      DFinsupp.lsum ℤ (fun i => ((s.inj i).f j).hom) (DFinsupp.single i x)
    rw [DFinsupp.lsum_single]
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.f j) (hm i)) x

end LittleFinitistic.DerivedSupport

end

end OAI
