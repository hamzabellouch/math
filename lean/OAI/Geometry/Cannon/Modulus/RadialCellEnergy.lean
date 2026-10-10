import Mathlib
import OAI.Geometry.Cannon.Modulus.ClosedCoverReflTrans
import OAI.Geometry.Cannon.Modulus.Weights
import OAI.Geometry.Cannon.PlanarGraphs.RadialIncidenceLength

namespace OAI

section
section
section
section
section
open MeasureTheory Set
open scoped BigOperators

namespace CannonRadialEnergy

attribute [local instance] Classical.propDecidable

theorem radial_cell_energy {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (p : X) (c : ι → X) (r w : ι → ℝ) (U : ι → Set X)
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcell : ∀ i, U i ⊆ Metric.closedBall (c i) (A*r i))
    (hadm : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if (U i ∩ Metric.sphere p t).Nonempty then w i else 0) :
    (b-a)^2 ≤ 4*A^2*(∑ i, r i^2)*∑ i, w i^2 := by
  classical
  apply radial_incidence_energy hab hA (fun i => dist p (c i)) r w hr hw
  intro t ht
  apply (hadm t ht).trans
  apply Finset.sum_le_sum
  intro i hi
  by_cases hu : (U i ∩ Metric.sphere p t).Nonempty
  · have hu₀ := hu
    rcases hu with ⟨x,hx,hxt⟩
    have hd : dist x p=t := hxt
    have hxc : dist x (c i) ≤ A*r i := hcell i hx
    have hrad : |t-dist p (c i)| ≤ A*r i := by
      simpa only [hd, dist_comm (c i) p] using (abs_dist_sub_le x (c i) p).trans hxc
    simp only [hrad,hu₀,ite_eq_left,le_refl]
  · rw [ite_eq_right hu]
    split_ifs
    · exact hw i
    · exact le_rfl

theorem radial_cell_energy_budget {ι X : Type*} [Fintype ι] [PseudoMetricSpace X]
    {a b A P : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (p : X) (c : ι → X) (r w : ι → ℝ) (U : ι → Set X)
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hcell : ∀ i, U i ⊆ Metric.closedBall (c i) (A*r i))
    (hbudget : (∑ i, r i^2) ≤ P)
    (hadm : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if (U i ∩ Metric.sphere p t).Nonempty then w i else 0) :
    (b-a)^2 ≤ 4*A^2*P*∑ i, w i^2 := by
  apply (radial_cell_energy hab hA p c r w U hr hw hcell hadm).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbudget (by positivity))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end CannonRadialEnergy

namespace CannonRadialEnergy
attribute [local instance] Classical.propDecidable

theorem disjoint_disk_square_budget {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (r : ι → ℝ) (p : ℂ) {R : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hR : 0 ≤ R)
    (hdisj : Pairwise (fun i j => Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))))
    (hcontain : ∀ i, Metric.ball (c i) (r i) ⊆ Metric.ball p R) :
    (∑ i, r i^2) ≤ R^2 := by
  classical
  have harea (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
      volume.real (Metric.ball z s) = s^2*Real.pi := by
    simp [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hs]
  have hU : (⋃ i ∈ (Finset.univ : Finset ι), Metric.ball (c i) (r i)) ⊆ Metric.ball p R := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i,hi⟩
    rcases mem_iUnion.mp hi with ⟨_,hxi⟩
    exact hcontain i hxi
  have hs : volume.real (⋃ i ∈ (Finset.univ : Finset ι), Metric.ball (c i) (r i)) =
      ∑ i, volume.real (Metric.ball (c i) (r i)) := by
    apply measureReal_biUnion_finset
    · intro i hi j hj hij
      exact hdisj hij
    · exact fun _ _ => Metric.isOpen_ball.measurableSet
    · intro i hi
      rw [Complex.volume_ball]
      finiteness
  have hh := measureReal_mono (μ := volume) hU (by rw [Complex.volume_ball]; finiteness)
  rw [hs,harea p hR] at hh
  simp only [harea _ (hr _)] at hh
  rw [← Finset.sum_mul] at hh
  nlinarith [Real.pi_pos]

theorem disk_realization_radial_energy {ι : Type*} [Fintype ι]
    {a b A R : ℝ} (hab : a ≤ b) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (p q : ℂ) (c : ι → ℂ) (r w : ι → ℝ) (U : ι → Set ℂ)
    (hr : ∀ i, 0 ≤ r i) (hw : ∀ i, 0 ≤ w i)
    (hdisj : Pairwise (fun i j => Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))))
    (hcontain : ∀ i, Metric.ball (c i) (r i) ⊆ Metric.ball q R)
    (hcell : ∀ i, U i ⊆ Metric.closedBall (c i) (A*r i))
    (hadm : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if (U i ∩ Metric.sphere p t).Nonempty then w i else 0) :
    (b-a)^2 ≤ 4*A^2*R^2*∑ i, w i^2 := by
  exact radial_cell_energy_budget hab hA p c r w U hr hw hcell
    (disjoint_disk_square_budget c r q hr hR hdisj hcontain) hadm

end CannonRadialEnergy

end

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace CannonRadialEnergy
open CannonCells CannonDuality

theorem disk_radial_modulus_lower {ι : Type*} [Fintype ι]
    {a b A R : ℝ} (hab : a ≤ b) (hA : 0 < A) (hR : 0 < R)
    (p q : ℂ) (c : ι → ℂ) (r : ι → ℝ) (U : ι → Set ℂ)
    (hr : ∀ i, 0 ≤ r i)
    (hdisj : Pairwise (fun i j => Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))))
    (hcontain : ∀ i, Metric.ball (c i) (r i) ⊆ Metric.ball q R)
    (hcell : ∀ i, U i ⊆ Metric.closedBall (c i) (A*r i))
    (hcover : ∀ t ∈ Icc a b, ∃ i, (Metric.sphere p t ∩ U i).Nonempty) :
    (b-a)^2/(4*A^2*R^2) ≤
      CannonCells.modulus U (Metric.sphere p '' Icc a b) := by
  classical
  let F : Set (Set ℂ) := Metric.sphere p '' Icc a b
  have hpos : 0 < 4*A^2*R^2 := by positivity
  have hone : Admissible (familyVectors U F : Set (Weights ι))
      (WithLp.toLp 2 (fun _ : ι => (1 : ℝ))) := by
    rw [admissible_iff]
    constructor
    · intro i
      exact zero_le_one
    · rintro _ ⟨t,ht,rfl⟩
      obtain ⟨i,hi⟩ := hcover t ht
      have hmem : i ∈ indices U (Metric.sphere p t) := (mem_indices _ _ _).2 hi
      have hle := Finset.single_le_sum (f := fun _ : ι => (1 : ℝ))
        (fun _ _ => zero_le_one) hmem
      exact hle
  change _ ≤ sInf {e : ℝ | ∃ w : Weights ι,
    Admissible (familyVectors U F : Set (Weights ι)) w ∧ e=‖w‖^2}
  apply le_csInf
  · exact ⟨_,⟨_,hone,rfl⟩⟩
  · rintro e ⟨w,hw,rfl⟩
    obtain ⟨hw₀,hadm⟩ := (admissible_iff U F w).1 hw
    have he := disk_realization_radial_energy hab hA.le hR.le p q c r (fun i => w i) U
      hr hw₀ hdisj hcontain hcell ?_
    · have hnorm : ‖w‖^2=∑ i, (w i)^2 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [Real.norm_eq_abs,sq_abs]
      rw [hnorm]
      exact (div_le_iff₀ hpos).2 (by nlinarith [he])
    · intro t ht
      have htF : Metric.sphere p t ∈ F := ⟨t,ht,rfl⟩
      have hh := hadm _ htF
      simpa only [indices,Finset.sum_filter,inter_comm] using hh

end CannonRadialEnergy

namespace CannonCells
open Set CannonDuality

variable {X Y ι : Type*} [Fintype ι]

lemma indices_image_preimage (f : X → Y) (C : ι → Set X) (A : Set Y) :
    indices (fun i => f '' C i) A = indices C (f ⁻¹' A) := by
  classical
  ext i
  rw [mem_indices,mem_indices]
  constructor
  · rintro ⟨y,hy,⟨x,hx,rfl⟩⟩
    exact ⟨x,hy,hx⟩
  · rintro ⟨x,hx,hC⟩
    exact ⟨f x,hx,⟨x,hC,rfl⟩⟩

theorem modulus_image_preimage (f : X → Y) (C : ι → Set X) (F : Set (Set Y)) :
    modulus (fun i => f '' C i) F = modulus C ((fun A => f ⁻¹' A) '' F) := by
  classical
  have he : familyVectors (fun i => f '' C i) F =
      familyVectors C ((fun A => f ⁻¹' A) '' F) := by
    ext v
    rw [mem_familyVectors,mem_familyVectors]
    constructor
    · rintro ⟨A,hA,hv⟩
      refine ⟨f ⁻¹' A,⟨A,hA,rfl⟩,?_⟩
      simpa only [incidence,indices_image_preimage] using hv
    · rintro ⟨_,⟨A,hA,rfl⟩,hv⟩
      refine ⟨A,hA,?_⟩
      simpa only [incidence,indices_image_preimage] using hv
  simp only [modulus,he]

end CannonCells

namespace CannonRadialEnergy
open Set CannonDuality CannonCells

theorem source_radial_modulus_lower {X ι : Type*} [Fintype ι]
    {a b A R : ℝ} (hab : a ≤ b) (hA : 0 < A) (hR : 0 < R)
    (C : ι → Set X) (F : Set (Set X)) (f : X → ℂ)
    (hC : ∀ x, ∃ i, x ∈ C i) (hFn : ∀ K ∈ F, K.Nonempty)
    (p q : ℂ) (c : ι → ℂ) (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i)
    (hdisj : Pairwise (fun i j => Disjoint (Metric.ball (c i) (r i))
      (Metric.ball (c j) (r j))))
    (hcontain : ∀ i, Metric.ball (c i) (r i) ⊆ Metric.ball q R)
    (hcell : ∀ i, f '' C i ⊆ Metric.closedBall (c i) (A*r i))
    (hcross : ∀ t ∈ Icc a b, ∃ K ∈ F, K ⊆ f ⁻¹' Metric.sphere p t) :
    (b-a)^2/(4*A^2*R^2) ≤ CannonCells.modulus C F := by
  classical
  have hF : F.Nonempty := by
    obtain ⟨K,hK,_⟩ := hcross a ⟨le_rfl,hab⟩
    exact ⟨K,hK⟩
  obtain ⟨_,w,hw,he⟩ := modulus_minimum C hC hF hFn
  obtain ⟨hw₀,hadm⟩ := (admissible_iff C F w).1 hw
  have hrad : ∀ t ∈ Icc a b,
      1 ≤ ∑ i, if ((f '' C i) ∩ Metric.sphere p t).Nonempty then w i else 0 := by
    intro t ht
    obtain ⟨K,hK,hsub⟩ := hcross t ht
    have hisub : indices C K ⊆ indices C (f ⁻¹' Metric.sphere p t) := by
      intro i hi
      obtain ⟨x,hx,hxi⟩ := (mem_indices _ _ _).1 hi
      exact (mem_indices _ _ _).2 ⟨x,hsub hx,hxi⟩
    have hh := (hadm K hK).trans (Finset.sum_le_sum_of_subset_of_nonneg hisub
      (fun i _ _ => hw₀ i))
    rw [← indices_image_preimage f C (Metric.sphere p t)] at hh
    simpa only [indices,Finset.sum_filter,inter_comm] using hh
  have henergy := disk_realization_radial_energy hab hA.le hR.le p q c r
    (fun i => w i) (fun i => f '' C i) hr hw₀ hdisj hcontain hcell hrad
  have hnorm : ‖w‖^2=∑ i, (w i)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  rw [← hnorm,he] at henergy
  exact (div_le_iff₀ (show 0 < 4*A^2*R^2 by positivity)).2 (by nlinarith [henergy])

end CannonRadialEnergy

end
end
end
section
noncomputable section

namespace CannonTransfer
theorem overlap_energy {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (R : α → Finset β) (w : β → ℝ) (kr kc : ℕ)
    (hrow : ∀ i, (R i).card ≤ kr)
    (hcol : ∀ j, (Finset.univ.filter (fun i => j ∈ R i)).card ≤ kc) :
    (∑ i, (∑ j ∈ R i, w j)^2) ≤
      (kr : ℝ) * kc * (∑ j, (w j)^2) := by
  classical
  have hrowE (i : α) : (∑ j ∈ R i, w j)^2 ≤ (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (R i) (fun _ => (1:ℝ)) w
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hrow i)
      (Finset.sum_nonneg (fun j _ => sq_nonneg (w j))))
  have hswap : (∑ i, ∑ j ∈ R i, (w j)^2) =
      ∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2 := by
    calc
      _ = ∑ i, ∑ j : β, if j ∈ R i then (w j)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        simp
      _ = ∑ j, ∑ i ∈ Finset.univ.filter (fun i => j ∈ R i), (w j)^2 := by
        simp only [Finset.sum_filter]
        rw [Finset.sum_comm]
      _ = _ := by simp
  calc
    _ ≤ ∑ i, (kr : ℝ) * (∑ j ∈ R i, (w j)^2) := Finset.sum_le_sum (fun i _ => hrowE i)
    _ = (kr : ℝ) * (∑ i, ∑ j ∈ R i, (w j)^2) := (Finset.mul_sum ..).symm
    _ = (kr : ℝ) * (∑ j, ((Finset.univ.filter (fun i => j ∈ R i)).card : ℝ) * (w j)^2) := by rw [hswap]
    _ ≤ (kr : ℝ) * (∑ j, (kc : ℝ) * (w j)^2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
        (by exact_mod_cast hcol j) (sq_nonneg (w j)))
    _ = _ := by rw [← Finset.mul_sum]; ring

end CannonTransfer

end
end
section
noncomputable section
open Set Metric Topology
open scoped BigOperators
open Classical

attribute [local instance] Classical.propDecidable
namespace CannonCarrierCharging

lemma sum_le_charges {ι ν : Type*} [DecidableEq ι] [DecidableEq ν]
    (I : Finset ι) (A : Finset ν) (R : ν → Finset ι) (w : ι → ℝ)
    (hw : ∀ i,0≤w i) (hcover : ∀ i∈I,∃ v∈A,i∈R v) :
    (∑ i∈I,w i)≤∑ v∈A,∑ i∈R v,w i := by
  have hi (i : ι) (hi : i∈I) : w i≤∑ v∈A,if i∈R v then w i else 0 := by
    obtain ⟨v,hv,hiv⟩:=hcover i hi
    have hh:=Finset.single_le_sum (s:=A) (f:=fun v=>if i∈R v then w i else 0)
      (fun v _=>by split; exact hw i; exact le_rfl) hv
    simpa only [ite_eq_left hiv] using hh
  calc
    _ ≤ ∑ i∈I,∑ v∈A,if i∈R v then w i else 0 := Finset.sum_le_sum hi
    _ = ∑ v∈A,∑ i∈I,if i∈R v then w i else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro v _
      rw [←Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi=>(Finset.mem_filter.mp hi).2) (fun i _ _=>hw i)

theorem path_cell_charging {X Y ι ν κ : Type*} [MetricSpace X]
    [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]
    (A : κ → Set X) (K : κ → Set Y) (U : ν → Set Y)
    (s : κ → ν) (v : ν → X) (q : ι → X) (S : Set Y)
    (mesh η D : ℝ)
    (hdiam : ∀ d,∀ x∈A d,dist x (v (s d))≤D)
    (hstar : ∀ d,K d⊆U (s d))
    {x y : X} (γ : Path x y)
    (hγ : range γ⊆thickening η (⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val))
    (w : ι → ℝ) (hw : ∀ i,0≤w i) :
    (∑ i∈CannonCells.indices (fun i=>ball (q i) (2*mesh)) (range γ),w i) ≤
      ∑ j∈Finset.univ.filter (fun j=>(S∩U j).Nonempty),
        ∑ i∈Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D),w i := by
  classical
  apply sum_le_charges _ _ _ _ hw
  intro i hi
  obtain ⟨z,hzγ,hzq⟩:=(CannonCells.mem_indices _ _ _).mp hi
  obtain ⟨a,ha,hza⟩:=mem_thickening_iff.mp (hγ hzγ)
  obtain ⟨d,had⟩:=mem_iUnion.mp ha
  refine ⟨s d.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  · obtain ⟨b,hbS,hbK⟩:=d.property
    exact ⟨b,hbS,hstar d.val hbK⟩
  · have hdist:=dist_triangle (q i) z (v (s d.val))
    have hdist':=dist_triangle z a (v (s d.val))
    have hd:=hdiam d.val a had
    have hz:=mem_ball.mp hzq
    rw [dist_comm z (q i)] at hz
    linarith

theorem carrier_admissible_charging {X Y ι ν κ : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν]
    (A : κ → Set X) (K : κ → Set Y) (U : ν → Set Y)
    (s : κ → ν) (v : ν → X) (q : ι → X) (S : Set Y)
    (mesh η D : ℝ) (hη : 0<η)
    (hdiam : ∀ d,∀ x∈A d,dist x (v (s d))≤D)
    (hstar : ∀ d,K d⊆U (s d))
    (hconn : IsPreconnected (⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val))
    {x y : X}
    (hx : x∈⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val)
    (hy : y∈⋃ (d : {d : κ // (S∩K d).Nonempty}),A d.val)
    (F : Set (Set X)) (hF : ∀ γ : Path x y,range γ∈F)
    (w : CannonDuality.Weights ι)
    (hw : CannonDuality.Admissible (CannonCells.familyVectors
      (fun i=>ball (q i) (2*mesh)) F : Set (CannonDuality.Weights ι)) w) :
    1≤∑ j∈Finset.univ.filter (fun j=>(S∩U j).Nonempty),
      ∑ i∈Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D),w i := by
  obtain ⟨γ,hγ⟩:=CannonFiniteCarrier.path_in_open_enlargement hconn
    isOpen_thickening (self_subset_thickening hη _) hx hy
  obtain ⟨hw0,hw1⟩:=(CannonCells.admissible_iff _ _ _).mp hw
  apply (hw1 (range γ) (hF γ)).trans
  apply path_cell_charging A K U s v q S mesh η D hdiam hstar γ _ (fun i=>w i) hw0
  rintro _ ⟨t,rfl⟩
  exact hγ t
end CannonCarrierCharging

namespace CannonCarrierCharging
open CannonCells CannonDuality

theorem radial_carrier_modulus_bound {X ι ν κ : Type*} [MetricSpace X]
    [LocallyPathConnectedSpace X] [Fintype ι] [Fintype ν]
    [DecidableEq ι] [DecidableEq ν]
    (A : κ → Set X) (K : κ → Set ℂ) (U : ν → Set ℂ)
    (s : κ → ν) (v : ν → X) (q : ι → X)
    (mesh η D : ℝ) (hη : 0<η)
    (hdiam : ∀ d,∀ x∈A d,dist x (v (s d))≤D)
    (hstar : ∀ d,K d⊆U (s d))
    (F : Set (Set X)) (hFn : ∀ E∈F,E.Nonempty)
    (hcover : ∀ x,∃ i,x∈ball (q i) (2*mesh))
    {a b L R : ℝ} (hab : a≤b) (hL : 0≤L) (hR : 0≤R)
    (p c0 : ℂ) (c : ν → ℂ) (rad : ν → ℝ)
    (hr : ∀ j,0≤rad j)
    (hdisj : Pairwise (fun i j=>Disjoint (ball (c i) (rad i)) (ball (c j) (rad j))))
    (hcontain : ∀ j,ball (c j) (rad j)⊆ball c0 R)
    (hcell : ∀ j,U j⊆closedBall (c j) (L*rad j))
    (hconn : ∀ t∈Icc a b,IsPreconnected
      (⋃ (d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val))
    (hcross : ∀ t∈Icc a b,
      ∃ x∈⋃ (d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
      ∃ y∈⋃ (d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
        ∀ γ : Path x y,range γ∈F)
    (kr kc : ℕ)
    (hrow : ∀ j,(Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D)).card≤kr)
    (hcol : ∀ i,(Finset.univ.filter (fun j=>dist (q i) (v j)<2*mesh+η+D)).card≤kc) :
    (b-a)^2≤4*L^2*R^2*(kr:ℝ)*kc*modulus (fun i=>ball (q i) (2*mesh)) F := by
  classical
  have hF : F.Nonempty := by
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross a ⟨le_rfl,hab⟩
    obtain ⟨γ,-⟩:=CannonFiniteCarrier.path_in_open_enlargement (hconn a ⟨le_rfl,hab⟩)
      isOpen_thickening (self_subset_thickening hη _) hx hy
    exact ⟨range γ,hxy γ⟩
  obtain ⟨_,w,hw,he⟩:=modulus_minimum (fun i=>ball (q i) (2*mesh)) hcover hF hFn
  let J : ν → Finset ι:=fun j=>Finset.univ.filter (fun i=>dist (q i) (v j)<2*mesh+η+D)
  let W : ν → ℝ:=fun j=>∑ i∈J j,w i
  have hW : ∀ j,0≤W j := fun j=>Finset.sum_nonneg fun i _=>hw.1 i
  have hadm : ∀ t∈Icc a b,1≤∑ j,if (U j∩sphere p t).Nonempty then W j else 0 := by
    intro t ht
    obtain ⟨x,hx,y,hy,hxy⟩:=hcross t ht
    have hh:=carrier_admissible_charging A K U s v q (sphere p t) mesh η D hη hdiam hstar
      (hconn t ht) hx hy F hxy w hw
    simpa only [W,J,Finset.sum_filter,inter_comm] using hh
  have hrad:=CannonRadialEnergy.disk_realization_radial_energy hab hL hR p c0 c rad W U
    hr hW hdisj hcontain hcell hadm
  have heW:=CannonTransfer.overlap_energy J (fun i=>w i) kr kc hrow (by
    intro i
    simpa only [J,Finset.mem_filter,Finset.mem_univ,true_and] using hcol i)
  have hnorm : ∑ i,(w i)^2=‖w‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ 4*L^2*R^2*∑ j,W j^2 := hrad
    _ ≤ 4*L^2*R^2*((kr:ℝ)*kc*∑ i,(w i)^2) :=
      mul_le_mul_of_nonneg_left heW (by positivity)
    _ = _ := by rw [hnorm,he]; ring
end CannonCarrierCharging

end
end
end
end

end OAI
