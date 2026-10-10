import Mathlib
import OAI.Geometry.Cannon.Modulus.RadialCellEnergy

namespace OAI

section
noncomputable section
open Set Metric Topology
open scoped BigOperators OnePoint

namespace CannonRadialEnergy
attribute [local instance] Classical.propDecidable
open Set Metric

theorem clipped_radial_energy {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    (K : ι → Set X) (c : ι → X) (r w : ι → ℝ) (good : ι → Prop)
    (hr : ∀ i,0≤r i) (hw : ∀ i,0≤w i)
    (p : X) {a b R P : ℝ} (hab : a≤b) (hb : b≤R) (hR : 0≤R)
    (hcell : ∀ i,good i → K i⊆closedBall (c i) (3*r i))
    (hbudget : (∑ i,if good i ∧ (K i∩closedBall p R).Nonempty then
      (min (r i) R)^2 else 0)≤P)
    (D : ℕ) (hbad : (Finset.univ.filter (fun i=>¬good i)).card≤D)
    (hadm : ∀ t∈Icc a b,1≤∑ i,if (K i∩sphere p t).Nonempty then w i else 0) :
    (b-a)^2≤36*(P+(D:ℝ)*R^2)*∑ i,w i^2 := by
  classical
  let act (i : ι) := (K i∩closedBall p R).Nonempty
  let U (i : ι) := K i∩closedBall p R
  let rad (i : ι) := if act i then (if good i then min (r i) R else R) else 0
  let cen (i : ι) := if good i ∧ r i≤R then c i else p
  have hrad (i : ι) : 0≤rad i := by
    dsimp [rad]
    split_ifs
    · exact le_min (hr i) hR
    · exact hR
    · exact le_rfl
  have hU (i : ι) : U i⊆closedBall (cen i) (3*rad i) := by
    intro x hx
    have ha : act i:=⟨x,hx⟩
    dsimp [rad,cen]
    rw [ite_eq_left ha]
    by_cases hg : good i
    · rw [ite_eq_left hg]
      by_cases hrR : r i≤R
      · rw [ite_eq_left ⟨hg,hrR⟩,min_eq_left hrR]
        exact hcell i hg hx.1
      · rw [ite_eq_right (fun h=>hrR h.2),min_eq_right (le_of_not_ge hrR)]
        exact (mem_closedBall.mp hx.2).trans (by linarith)
    · rw [ite_eq_right hg,ite_eq_right (fun h=>hg h.1)]
      exact (mem_closedBall.mp hx.2).trans (by linarith)
  have hbud : (∑ i,rad i^2)≤P+(D:ℝ)*R^2 := by
    have he (i : ι) : rad i^2 ≤
        (if good i ∧ act i then (min (r i) R)^2 else 0)+
        (if ¬good i then R^2 else 0) := by
      by_cases ha : act i <;> by_cases hg : good i <;> simp [rad,ha,hg,sq_nonneg]
    calc
      _ ≤ ∑ i,((if good i ∧ act i then (min (r i) R)^2 else 0)+
          (if ¬good i then R^2 else 0)) := Finset.sum_le_sum (fun i _=>he i)
      _ = (∑ i,if good i ∧ act i then (min (r i) R)^2 else 0)+
          ((Finset.univ.filter (fun i=>¬good i)).card:ℝ)*R^2 := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [←Finset.sum_filter]
        simp
      _ ≤ P+(D:ℝ)*R^2 := add_le_add hbudget
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hbad) (sq_nonneg R))
  have hadm' : ∀ t∈Icc a b,1≤∑ i,if (U i∩sphere p t).Nonempty then w i else 0 := by
    intro t ht
    convert hadm t ht using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply propext
    constructor
    · rintro ⟨x,⟨hx,-⟩,hxt⟩
      exact ⟨x,hx,hxt⟩
    · rintro ⟨x,hx,hxt⟩
      exact ⟨x,⟨hx,(mem_sphere.mp hxt).le.trans (ht.2.trans hb)⟩,hxt⟩
  have hh:=radial_cell_energy_budget hab (show (0:ℝ)≤3 by norm_num) p cen rad w U
    hrad hw hU hbud hadm'
  norm_num at hh ⊢
  exact hh
end CannonRadialEnergy

namespace CannonCarrierCharging
open CannonCells CannonDuality

attribute [local instance] Classical.propDecidable

theorem clipped_spherical_carrier_modulus {X ι κ : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (A : κ → Set X) (K : κ → Set (OnePoint ℂ)) (v : κ → X) (q : ι → X)
    (mesh η diam : ℝ) (hη : 0<η)
    (hdiam : ∀ d,∀ x∈A d,dist x (v d)≤diam)
    (F : Set (Set X)) (hFn : ∀ E∈F,E.Nonempty)
    (hcover : ∀ x,∃ i,x∈ball (q i) (2*mesh))
    (c : κ → ℂ) (rad : κ → ℝ) (good : κ → Prop)
    (hr : ∀ d,0≤rad d) (p : ℂ) {a b R : ℝ}
    (hab : a≤b) (hb : b≤R) (hR : 0≤R) (D : ℕ)
    (hcell : ∀ d,good d → ((↑) : ℂ → OnePoint ℂ) ⁻¹' K d⊆closedBall (c d) (3*rad d))
    (hbudget : (∑ d,if good d ∧ ((((↑) : ℂ → OnePoint ℂ) ⁻¹' K d)∩closedBall p R).Nonempty
      then (min (rad d) R)^2 else 0)≤(25*(D:ℝ)+1)*R^2)
    (hbad : (Finset.univ.filter (fun d=>¬good d)).card≤D)
    (hconn : ∀ t∈Icc a b,IsPreconnected
      (⋃ (d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val))
    (hcross : ∀ t∈Icc a b,
      ∃ x∈⋃ (d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
      ∃ y∈⋃ (d : {d : κ // (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty}),A d.val,
        ∀ γ : Path x y,range γ∈F)
    (kr kc : ℕ)
    (hrow : ∀ d,(Finset.univ.filter (fun i=>dist (q i) (v d)<2*mesh+η+diam)).card≤kr)
    (hcol : ∀ i,(Finset.univ.filter (fun d=>dist (q i) (v d)<2*mesh+η+diam)).card≤kc) :
    (b-a)^2≤36*(26*(D:ℝ)+1)*R^2*(kr:ℝ)*kc*modulus (fun i=>ball (q i) (2*mesh)) F := by
  classical
  have hF : F.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross a ⟨le_rfl,hab⟩
    obtain ⟨γ,-⟩:=CannonFiniteCarrier.path_in_open_enlargement (hconn a ⟨le_rfl,hab⟩)
      isOpen_thickening (self_subset_thickening hη _) hx hy
    exact ⟨range γ,hxy γ⟩
  obtain ⟨_,w,hw,he⟩:=modulus_minimum (fun i=>ball (q i) (2*mesh)) hcover hF hFn
  let J : κ → Finset ι:=fun d=>Finset.univ.filter (fun i=>dist (q i) (v d)<2*mesh+η+diam)
  let W : κ → ℝ:=fun d=>∑ i∈J d,w i
  have hW : ∀ d,0≤W d:=fun d=>Finset.sum_nonneg fun i _=>hw.1 i
  have hiff (d : κ) (t : ℝ) :
      (((↑) '' sphere p t : Set (OnePoint ℂ))∩K d).Nonempty ↔
      ((((↑) : ℂ → OnePoint ℂ) ⁻¹' K d)∩sphere p t).Nonempty := by
    constructor
    · rintro ⟨x,⟨z,hz,rfl⟩,hx⟩
      exact ⟨z,hx,hz⟩
    · rintro ⟨z,hz,hzt⟩
      exact ⟨(z:OnePoint ℂ),⟨z,hzt,rfl⟩,hz⟩
  have hadm : ∀ t∈Icc a b,1≤∑ d,if ((((↑) : ℂ → OnePoint ℂ) ⁻¹' K d)∩sphere p t).Nonempty
      then W d else 0 := by
    intro t ht
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross t ht
    have hh:=carrier_admissible_charging A K K id v q ((↑) '' sphere p t : Set (OnePoint ℂ))
      mesh η diam hη hdiam (fun _=>Subset.rfl) (hconn t ht) hx hy F hxy w hw
    simpa only [W,J,Finset.sum_filter,hiff] using hh
  have hrad:=CannonRadialEnergy.clipped_radial_energy
    (fun d=>((↑) : ℂ → OnePoint ℂ) ⁻¹' K d) c rad W good hr hW p hab hb hR hcell hbudget D hbad hadm
  have heW:=CannonTransfer.overlap_energy J (fun i=>w i) kr kc hrow (by
    intro i
    simpa only [J,Finset.mem_filter,Finset.mem_univ,true_and] using hcol i)
  have hnorm : ∑ i,(w i)^2=‖w‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ 36*((25*(D:ℝ)+1)*R^2+(D:ℝ)*R^2)*∑ d,W d^2 := hrad
    _ ≤ 36*((25*(D:ℝ)+1)*R^2+(D:ℝ)*R^2)*((kr:ℝ)*kc*∑ i,(w i)^2) :=
      mul_le_mul_of_nonneg_left heW (by positivity)
    _ = _ := by rw [hnorm,he]; ring
end CannonCarrierCharging

end
end

end OAI
