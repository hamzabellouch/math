import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Sheaves.PlaneModules

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.LaurentPlane

variable {K : Type} [Field K] {A B C W : Scheme.{0}}

theorem three_chart_quotient_finite [IsAffine A] [IsAffine B] [IsAffine C]
    (kA : K →+* Γ(A,⊤)) (kB : K →+* Γ(B,⊤))
    (kC : K →+* Γ(C,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ A) (b : W ⟶ B) (c : W ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (hka : a.appTop.hom.comp kA = kW) (hkb : b.appTop.hom.comp kB = kW)
    (hkc : c.appTop.hom.comp kC = kW)
    (LA : LineBundle A) (LB : LineBundle B) (LC : LineBundle C) (N : W.Modules)
    (ea : LA.sheaf.restrict a ≅ N) (eb : LB.sheaf.restrict b ≅ N)
    (ec : LC.sheaf.restrict c ≅ N)
    (u v : Γ(W,⊤)ˣ)
    (ax : Γ(A,⊤)ˣ) (ay : Γ(A,⊤)) (bx : Γ(B,⊤)) (by' : Γ(B,⊤)ˣ)
    (cx : Γ(C,⊤)ˣ) (cy : Γ(C,⊤))
    (hax : Units.map a.appTop.hom ax = u) (hay : a.appTop ay = v)
    (hbx : b.appTop bx = u) (hby : Units.map b.appTop.hom by' = v)
    (hcx : Units.map c.appTop.hom cx = u*v⁻¹) (hcy : c.appTop cy = ↑(v⁻¹))
    (ha : a.opensRange = A.basicOpen ay) (hb : b.opensRange = B.basicOpen bx)
    (hc : c.opensRange = C.basicOpen cy)
    (hfin : letI := laurentModule kW u v N
      Module.Finite (LaurentPlane.Ring K) (Sections kW N ⊤)) :
    Module.Finite K (Sections kW N ⊤ ⧸
      (((chartMap kA kW a hka LA.sheaf ea).range ⊔
        (chartMap kB kW b hkb LB.sheaf eb).range) ⊔
        (chartMap kC kW c hkc LC.sheaf ec).range)) := by
  let := laurentModule kW u v N
  let := laurentTower kW u v N
  let := hfin
  apply LaurentPlane.quotient_finite
  · intro z hz
    apply chartMap_monomial_mem kA kW a hka LA.sheaf ea u v z
    exact ⟨_,LaurentPlane.lift_cone_left kW u v a.appTop.hom ax ay hax hay z hz⟩
  · intro z hz
    apply chartMap_monomial_mem kB kW b hkb LB.sheaf eb u v z
    exact ⟨_,LaurentPlane.lift_cone_right kW u v b.appTop.hom bx by' hbx hby z hz⟩
  · intro z hz
    apply chartMap_monomial_mem kC kW c hkc LC.sheaf ec u v z
    exact ⟨_,LaurentPlane.lift_cone_top kW u v c.appTop.hom cx cy hcx hcy z hz⟩
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kA kW a hka LA.sheaf ea ay ha m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T (0,(n : ℤ))) • m ∈ _
    simpa only [eval_T, zpow_zero, one_mul, zpow_natCast, Units.val_pow_eq_pow_val, hay] using hn
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kB kW b hkb LB.sheaf eb bx hb m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T ((n : ℤ),0)) • m ∈ _
    simpa only [eval_T, zpow_zero, mul_one, zpow_natCast, Units.val_pow_eq_pow_val, hbx] using hn
  · intro m
    obtain ⟨n,hn⟩ := chartMap_clearing kC kW c hkc LC.sheaf ec cy hc m
    refine ⟨n,?_⟩
    change LaurentPlane.eval kW u v (T (0,-(n : ℤ))) • m ∈ _
    rw [eval_T]
    simp only [zpow_zero, one_mul, zpow_neg, zpow_natCast]
    rw [← inv_pow, Units.val_pow_eq_pow_val]
    simpa only [hcy] using hn

end
end MaximalSeshadri.Geometry.BaseSections

end


end OAI
