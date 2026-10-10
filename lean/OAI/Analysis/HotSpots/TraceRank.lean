import OAI.Analysis.HotSpots.Cauchy

namespace OAI

section ActualHilbertContradiction


section

noncomputable section
open Set Function
open scoped InnerProductSpace Topology
namespace StrictHotSpots.CircleGeometry

lemma continuous_exists_eq_antipodal (f : Circle → ℝ) (hf : Continuous f) :
    ∃ s, f s = f (-s) := by
  let h : Circle → ℝ := fun s => f s-f (-s)
  have hc : Continuous h := hf.sub (hf.comp continuous_neg)
  have hn (s : Circle) : h (-s) = -h s := by simp only [h,neg_neg]; ring
  have hx : 0 ∈ Set.range h := by
    apply mem_range_of_exists_le_of_exists_ge hc
    · by_cases hh : h 1 ≤ 0
      · exact ⟨1,hh⟩
      · exact ⟨-1,by rw [hn]; linarith⟩
    · by_cases hh : 0 ≤ h 1
      · exact ⟨1,hh⟩
      · exact ⟨-1,by rw [hn]; linarith⟩
  obtain ⟨s,hs⟩ := hx
  exact ⟨s,sub_eq_zero.mp hs⟩

lemma not_continuous_injective_to_real {f : Circle → ℝ} (hf : Continuous f) :
    ¬Injective f := by
  intro hi
  obtain ⟨s,hs⟩ := continuous_exists_eq_antipodal f hf
  exact Circle.neg_ne_self s (hi hs).symm


theorem not_subset_affine_line {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {b : Circle → H} (hb : Continuous b) (hi : Injective b) (a v : H) :
    ¬(∀ s, ∃ t : ℝ, b s = a+t•v) := by
  intro hline
  have hn : v ≠ 0 := by
    intro hz
    apply Circle.neg_ne_self (1 : Circle)
    apply hi
    obtain ⟨c,hc⟩ := hline (-1)
    obtain ⟨d,hd⟩ := hline 1
    simp only [hz,smul_zero,add_zero] at hc hd
    exact hc.trans hd.symm
  let f : Circle → ℝ := fun s => inner ℝ v (b s-a)
  apply not_continuous_injective_to_real (show Continuous f by fun_prop)
  intro s t hst
  obtain ⟨r,hr⟩ := hline s
  obtain ⟨q,hq⟩ := hline t
  have hne : inner ℝ v v ≠ 0 := inner_self_ne_zero.mpr hn
  have he : r=q := by
    change inner ℝ v (b s-a) = inner ℝ v (b t-a) at hst
    rw [hr,hq,add_sub_cancel_left,add_sub_cancel_left,real_inner_smul_right,
      real_inner_smul_right] at hst
    exact mul_right_cancel₀ hne hst
  apply hi
  rw [hr,hq,he]

end StrictHotSpots.CircleGeometry

end

section

noncomputable section
open Set Function Module
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

variable {S E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local instance : Nontrivial Circle := ⟨⟨-1,1,Circle.neg_ne_self 1⟩⟩

lemma coordinate_separates (e : HilbertBasis ι ℝ H) {x y : H} (h : x ≠ y) :
    ∃ i, inner ℝ (e i) x ≠ inner ℝ (e i) y := by
  by_contra! hh
  apply h
  apply e.repr.injective
  ext i
  simpa only [e.repr_apply_apply] using hh i

lemma pair_independent (T : Submodule ℝ (S → E)) (g : T) (a : S → ℝ)
    (ha : (fun s => a s • g.val s) ∈ T) {s t : S}
    (hs : g.val s ≠ 0) (ht : g.val t ≠ 0) (hst : a s ≠ a t) :
    LinearIndependent ℝ ![(⟨fun s => a s • g.val s,ha⟩ : T),g] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hz
    exact hs (congrArg (fun f : T => f.val s) hz)
  · intro c hc
    have hcs := congrArg (fun f : T => f.val s) hc
    have hct := congrArg (fun f : T => f.val t) hc
    change c • g.val s = a s • g.val s at hcs
    change c • g.val t = a t • g.val t at hct
    exact hst ((smul_left_injective ℝ hs hcs).symm.trans (smul_left_injective ℝ ht hct))

lemma rank_two_spanning {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {f g : V} (hr : finrank ℝ V ≤ 2)
    (hi : LinearIndependent ℝ ![f,g]) (v : V) : ∃ a c : ℝ, a • f+c • g=v := by
  have hn : Fintype.card (Fin 2) = finrank ℝ V := by
    have hh := hi.fintype_card_le_finrank
    simpa using (le_antisymm hh hr)
  have htop := hi.span_eq_top_of_card_eq_finrank' hn
  apply Submodule.mem_span_pair.mp
  have he : Set.range ![f,g] = ({f,g} : Set V) := by simp [Set.pair_comm]
  rw [← he,htop]
  trivial

lemma scalar_affine_elimination {A B C D P Q z : ℝ} (hne : P ≠ Q)
    (hA : A=C*P+D) (hB : B=C*Q+D) :
    C*z+D = A+((z-P)/(Q-P))*(B-A) := by
  have hd : Q-P ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [hA,hB]
  field_simp
  ring




theorem rank_two_affine_support (e : HilbertBasis ι ℝ H) (b : S → H)
    (T : Submodule ℝ (S → E)) [FiniteDimensional ℝ T] (hr : finrank ℝ T ≤ 2)
    (g : T) (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T)
    {s t : S} (hs : g.val s ≠ 0) (ht : g.val t ≠ 0) (hb : b s ≠ b t) :
    ∃ j, inner ℝ (e j) (b s) ≠ inner ℝ (e j) (b t) ∧
      ∀ x, g.val x ≠ 0 → b x = b s +
        ((inner ℝ (e j) (b x)-inner ℝ (e j) (b s)) /
          (inner ℝ (e j) (b t)-inner ℝ (e j) (b s))) • (b t-b s) := by
  obtain ⟨j,hj⟩ := coordinate_separates e hb
  let f : T := ⟨fun x => inner ℝ (e j) (b x) • g.val x,hmem j⟩
  have hi : LinearIndependent ℝ ![f,g] := pair_independent T g _ (hmem j) hs ht hj
  refine ⟨j,hj,?_⟩
  intro x hx
  apply e.repr.injective
  ext i
  simp only [e.repr_apply_apply,inner_add_right,real_inner_smul_right,inner_sub_right]
  obtain ⟨a,c,hac⟩ := rank_two_spanning hr hi (⟨fun y => inner ℝ (e i) (b y) • g.val y,hmem i⟩ : T)
  have he (y : S) (hy : g.val y ≠ 0) : inner ℝ (e i) (b y) = a*inner ℝ (e j) (b y)+c := by
    have hh := congrArg (fun f : T => f.val y) hac
    change a • (inner ℝ (e j) (b y) • g.val y)+c • g.val y =
      inner ℝ (e i) (b y) • g.val y at hh
    rw [smul_smul,← add_smul] at hh
    exact (smul_left_injective ℝ hy hh).symm
  rw [he x hx]
  exact scalar_affine_elimination hj (he s hs) (he t ht)

lemma nonempty_open_two_points {S : Type*} [TopologicalSpace S] [PerfectSpace S]
    {U : Set S} (hu : IsOpen U) (hne : U.Nonempty) :
    ∃ s ∈ U, ∃ t ∈ U, s ≠ t := by
  obtain ⟨s,hs⟩ := hne
  obtain ⟨t,ht,hst⟩ := preperfect_iff_nhds.mp PerfectSpace.univ_preperfect
    s (mem_univ s) U (hu.mem_nhds hs)
  exact ⟨s,hs,t,ht.1,hst.symm⟩



theorem not_dense_support_of_rank_two (e : HilbertBasis ι ℝ H)
    {b : Circle → H} (hb : Continuous b) (hi : Injective b)
    (T : Submodule ℝ (Circle → E)) [FiniteDimensional ℝ T] (hr : finrank ℝ T ≤ 2)
    (g : T) (hg : Continuous g.val)
    (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T) :
    ¬Dense {s | g.val s ≠ 0} := by
  intro hd
  have ho : IsOpen {s | g.val s ≠ 0} := isOpen_ne_fun hg continuous_const
  obtain ⟨s,hs,t,ht,hst⟩ := nonempty_open_two_points ho hd.nonempty
  obtain ⟨j,hj,hline⟩ := rank_two_affine_support e b T hr g hmem hs ht (hi.ne hst)
  have hall : b = fun x => b s +
      ((inner ℝ (e j) (b x)-inner ℝ (e j) (b s)) /
        (inner ℝ (e j) (b t)-inner ℝ (e j) (b s))) • (b t-b s) :=
    Continuous.ext_on hd hb (by fun_prop) hline
  apply CircleGeometry.not_subset_affine_line hb hi (b s) (b t-b s)
  intro x
  exact ⟨_,congrFun hall x⟩



theorem no_nonzero_multiplier_in_rank_one (e : HilbertBasis ι ℝ H)
    {b : Circle → H} (hi : Injective b)
    (T : Submodule ℝ (Circle → E)) [FiniteDimensional ℝ T] (hr : finrank ℝ T ≤ 1)
    (g : T) (hg : Continuous g.val)
    (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T) : g = 0 := by
  by_contra hz
  have hne : {s | g.val s ≠ 0}.Nonempty := by
    by_contra hh
    apply hz
    apply Subtype.ext
    funext s
    exact not_ne_iff.mp (fun hs => hh ⟨s,hs⟩)
  obtain ⟨s,hs,t,ht,hst⟩ := nonempty_open_two_points (isOpen_ne_fun hg continuous_const) hne
  obtain ⟨j,hj⟩ := coordinate_separates e (hi.ne hst)
  have hlin := pair_independent T g _ (hmem j) hs ht hj
  have hn := hlin.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hn
  omega

end StrictHotSpots.HilbertMultipliers

end

section

noncomputable section
open Set Function Module
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

variable {S E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]


def vanishingOn (T : Submodule ℝ (S → E)) (U : Set S) : Submodule ℝ (S → E) where
  carrier := {f | f ∈ T ∧ ∀ x ∈ U, f x = 0}
  zero_mem' := ⟨T.zero_mem,fun _ _ => rfl⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨T.add_mem hf.1 hg.1,fun x hx => by simp [hf.2 x hx,hg.2 x hx]⟩
  smul_mem' := by
    intro c f hf
    exact ⟨T.smul_mem c hf.1,fun x hx => by simp [hf.2 x hx]⟩

lemma vanishingOn_le (T : Submodule ℝ (S → E)) (U : Set S) : vanishingOn T U ≤ T :=
  fun _ hf => hf.1

instance (T : Submodule ℝ (S → E)) [FiniteDimensional ℝ T] (U : Set S) :
    FiniteDimensional ℝ (vanishingOn T U) :=
  FiniteDimensional.of_injective (Submodule.inclusion (vanishingOn_le T U))
    (Submodule.inclusion_injective (vanishingOn_le T U))




theorem multiplier_contradiction (e : HilbertBasis ι ℝ H)
    {b : Circle → H} (hb : Continuous b) (hi : Injective b)
    (T : Submodule ℝ (Circle → E)) [FiniteDimensional ℝ T]
    (hr : finrank ℝ T ≤ 2)
    (hloc : ∀ U : Set Circle, IsOpen U → U.Nonempty → finrank ℝ (vanishingOn T U) ≤ 1)
    (g : T) (hg : Continuous g.val)
    (hmem : ∀ i, (fun s => inner ℝ (e i) (b s) • g.val s) ∈ T) : g = 0 := by
  have hnd := not_dense_support_of_rank_two e hb hi T hr g hg hmem
  let U : Set Circle := (closure {s | g.val s ≠ 0})ᶜ
  have hU : IsOpen U := isClosed_closure.isOpen_compl
  have hne : U.Nonempty := by
    rw [dense_iff_closure_eq] at hnd
    exact Set.nonempty_compl.mpr hnd
  have hz (s : Circle) (hs : s ∈ U) : g.val s = 0 := by
    by_contra hn
    exact hs (subset_closure hn)
  let f : vanishingOn T U := ⟨g.val,g.property,hz⟩
  have hm (i : ι) : (fun s => inner ℝ (e i) (b s) • f.val s) ∈ vanishingOn T U := by
    refine ⟨hmem i,?_⟩
    intro s hs
    change inner ℝ (e i) (b s) • g.val s = 0
    rw [hz s hs,smul_zero]
  have hf := no_nonzero_multiplier_in_rank_one e hi (vanishingOn T U) (hloc U hU hne) f hg hm
  exact Subtype.ext (congrArg (fun w : vanishingOn T U => w.val) hf)

end StrictHotSpots.HilbertMultipliers

end
end
end
end
end ActualHilbertContradiction

section ClosedTraceRank

noncomputable section
open Set Function Module
open scoped Topology
namespace StrictHotSpots
open HilbertMultipliers


def closedGradientTrace {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1 →ₗ[ℝ] (Circle → Plane) where
  toFun J s := J.val.2 ⟨c.circleBoundaryHomeomorph s,(c.circleBoundaryHomeomorph s).property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def closedTraceSpace {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : Submodule ℝ (Circle → Plane) := (closedGradientTrace c hΩ).range

lemma closedTraceSpace_rank {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) : Module.Finite ℝ (closedTraceSpace c hΩ) ∧
      finrank ℝ (closedTraceSpace c hΩ) ≤ 2 := by
  obtain ⟨hf,hr⟩ := closedEigenSpace_finrank_le_two c hΩ
  let : Module.Finite ℝ (closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1) := hf
  refine ⟨?_,(LinearMap.finrank_range_le (closedGradientTrace c hΩ)).trans hr⟩
  change Module.Finite ℝ (closedGradientTrace c hΩ).range
  infer_instance

lemma closedTraceSpace_local_rank {Ω : Set Plane} (c : Conformal.ClosedDiskChart Ω)
    (hΩ : AdmissibleDomain Ω) {U : Set Circle} (hU : IsOpen U) (hne : U.Nonempty) :
    finrank ℝ (vanishingOn (closedTraceSpace c hΩ) U) ≤ 1 := by
  classical
  obtain ⟨O,hO,hOU⟩ := isOpen_induced_iff.mp (c.circleBoundaryHomeomorph.isOpenMap U hU)
  have hmem (s : Circle) : s ∈ U ↔ (c.circleBoundaryHomeomorph s : Plane) ∈ O := by
    have hh : c.circleBoundaryHomeomorph s ∈ c.circleBoundaryHomeomorph '' U ↔ s ∈ U :=
      c.circleBoundaryHomeomorph.injective.mem_set_image
    rw [← hOU] at hh
    exact hh.symm
  obtain ⟨s,hs⟩ := hne
  obtain ⟨hf,hr⟩ := closedPatchEigenSpace_finrank_le_one c hΩ
    (c.circleBoundaryHomeomorph s).property hO ((hmem s).mp hs)
  let : Module.Finite ℝ (closedPatchEigenSpace Ω O hΩ) := hf
  let E := closedEigenSpace Ω hΩ.2.1 hΩ.2.2.1
  let P := closedPatchEigenSpace Ω O hΩ
  let inc : P →ₗ[ℝ] E := Submodule.inclusion (fun _ h => h.1)
  let L := (closedGradientTrace c hΩ).comp inc
  have heq : L.range = vanishingOn (closedTraceSpace c hΩ) U := by
    ext g
    constructor
    · rintro ⟨J,rfl⟩
      refine ⟨⟨inc J,rfl⟩,?_⟩
      intro t ht
      exact J.property.2 _ ⟨(hmem t).mp ht,(c.circleBoundaryHomeomorph t).property⟩
    · rintro ⟨⟨J,hJ⟩,hz⟩
      have hpatch : J.val ∈ P := by
        refine ⟨J.property,?_⟩
        intro x hx
        let t := c.circleBoundaryHomeomorph.symm ⟨x,hx.2⟩
        have ht : (c.circleBoundaryHomeomorph t : Plane) = x :=
          congrArg Subtype.val (c.circleBoundaryHomeomorph.apply_symm_apply ⟨x,hx.2⟩)
        have htU : t ∈ U := (hmem t).mpr (ht ▸ hx.1)
        have hh := hz t htU
        rw [← hJ] at hh
        change J.val.2 ⟨c.circleBoundaryHomeomorph t,_⟩ = 0 at hh
        convert hh using 1
        exact congrArg J.val.2 (Subtype.ext ht.symm)
      refine ⟨⟨J.val,hpatch⟩,?_⟩
      exact hJ
  rw [← heq]
  exact (LinearMap.finrank_range_le L).trans hr
end StrictHotSpots
end
end ClosedTraceRank

section ClosedTraceNonzero

noncomputable section
open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
include c




theorem boundary_gradient_not_zero (hΩ : AdmissibleDomain Ω)
    {v : Plane → ℝ} (hv : InInteriorNeumannEigenspace Ω v)
    (hvc : ContinuousOn v (closure Ω)) {Y : Plane → Plane}
    (hY : ContinuousOn Y (closure Ω)) (he : EqOn (gradient v) Y Ω)
    (hne : ∃ x ∈ Ω, v x ≠ 0) : ¬ (∀ x ∈ frontier Ω, Y x = 0) := by
  intro hz
  have hd (x : Plane) (hx : x ∈ frontier Ω) :
      HasFDerivWithinAt v (0 : Plane →L[ℝ] ℝ) (closure Ω) x :=
    c.hasFDerivWithinAt_zero_of_closedGradient_zero hv.1 hvc hY he hx.1 (hz x hx)
  let f : Circle → ℝ := fun s => v (c.circleBoundaryHomeomorph s)
  have hmap : Continuous (fun s : Circle => (c.circleBoundaryHomeomorph s : Plane)) :=
    continuous_subtype_val.comp c.circleBoundaryHomeomorph.continuous
  have hc : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro s
    obtain ⟨V,hV,hsV,hconst⟩ := hΩ.2.2.2.2.locally_const_of_boundary_zero_jet hΩ.2.1
      (c.circleBoundaryHomeomorph s).property isOpen_univ (mem_univ _)
      (fun x hx => hd x hx.2)
    refine ⟨(fun s : Circle => (c.circleBoundaryHomeomorph s : Plane)) ⁻¹' V,
      hV.preimage hmap,hsV,?_⟩
    intro t ht
    exact hconst _ ⟨ht,(c.circleBoundaryHomeomorph t).property⟩
  obtain ⟨x,hx,hvx⟩ := InteriorBoundarySign.exists_boundary_pos hΩ.2.1 hΩ.2.2.1 hv hvc hne
  obtain ⟨y,hy,hvy⟩ := InteriorBoundarySign.exists_boundary_neg hΩ.2.1 hΩ.2.2.1 hv hvc hne
  have heq := hc.apply_eq_of_preconnectedSpace
    (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩) (c.circleBoundaryHomeomorph.symm ⟨y,hy⟩)
  change v (c.circleBoundaryHomeomorph (c.circleBoundaryHomeomorph.symm ⟨x,hx⟩)) =
    v (c.circleBoundaryHomeomorph (c.circleBoundaryHomeomorph.symm ⟨y,hy⟩)) at heq
  simp only [Homeomorph.apply_symm_apply] at heq
  linarith
end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedTraceNonzero



end OAI
