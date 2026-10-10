import Mathlib

namespace OAI

/-! Path lifting, simple connectivity and topological group sections. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawQuotientTopology
open unitInterval
variable {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

 

omit [IsTopologicalGroup Q] in
theorem exists_path_lift (π : G →* Q)
    (hsec : ∀ x : Q, ∃ U : Set Q, IsOpen U ∧ x ∈ U ∧ ∃ s : Q → G,
      ContinuousOn s U ∧ ∀ y ∈ U, π (s y) = y)
    (γ : C(I,Q)) (e : G) (he : π e = γ 0) :
    ∃ Γ : C(I,G), π ∘ Γ = γ ∧ Γ 0 = e := by
  classical
  choose U hU hx s hs hproj using hsec
  obtain ⟨t,t₀,tmono,⟨nmax,hmax⟩,hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun x => (hU x).preimage γ.continuous)
      (fun u _ => mem_iUnion.mpr ⟨γ u,hx _⟩)
  suffices ∀ n, ∃ Γ : I → G, ContinuousOn Γ (Icc 0 (t n)) ∧
      EqOn (π ∘ Γ) γ (Icc 0 (t n)) ∧ Γ 0 = e by
    obtain ⟨Γ,hΓ,hΓπ,hΓ0⟩ := this nmax
    rw [hmax _ le_rfl] at hΓ hΓπ
    refine ⟨⟨Γ,continuousOn_univ.mp ?_⟩, funext (fun u => hΓπ ⟨bot_le,le_top⟩),hΓ0⟩
    convert hΓ using 1
    ext u
    simp only [mem_univ, mem_Icc]
    exact ⟨fun _ => ⟨u.property.1,u.property.2⟩,fun _ => trivial⟩
  intro n
  induction n with
  | zero =>
    refine ⟨fun _ => e,continuous_const.continuousOn,?_,rfl⟩
    intro u hu
    rw [t₀,Icc_self,mem_singleton_iff] at hu
    subst u
    exact he
  | succ n ih =>
    obtain ⟨Γ,hΓ,hΓπ,hΓ0⟩ := ih
    obtain ⟨x,htx⟩ := hsub n
    have htn : π (Γ (t n)) = γ (t n) := hΓπ ⟨t₀ ▸ tmono n.zero_le,le_rfl⟩
    have htnU : γ (t n) ∈ U x := htx ⟨le_rfl,tmono n.le_succ⟩
    let L : I → G := fun u => Γ (t n) * (s x (γ (t n)))⁻¹ * s x (γ u)
    refine ⟨fun u => if u ≤ t n then Γ u else L u,
      ContinuousOn.if (fun u hu => ?_) (hΓ.mono (fun u hu => ?_)) ?_, ?_, ?_⟩
    · cases frontier_Iic_subset _ hu.2
      simp only [L, inv_mul_cancel_right]
    · rw [closure_le_eq continuous_id' continuous_const] at hu
      exact ⟨hu.1.1,hu.2⟩
    · apply continuousOn_const.mul
      apply (hs x).comp γ.continuous.continuousOn
      intro u hu
      exact htx ⟨closure_lt_subset_le (f := fun _ : I => t n) (g := fun u : I => u)
        continuous_const continuous_id' (by simpa only [not_le] using hu.2),hu.1.2⟩
    · intro u hu
      dsimp only [Function.comp_apply]
      split_ifs with h
      · exact hΓπ ⟨hu.1,h⟩
      · have huU : γ u ∈ U x := htx ⟨le_of_not_ge h,hu.2⟩
        simp only [L,map_mul,map_inv,htn,hproj x _ htnU,hproj x _ huU,mul_inv_cancel,one_mul]
    · dsimp only
      rwa [ite_eq_left (t₀ ▸ tmono n.zero_le)]

end RawQuotientTopology

namespace RawQuotientTopology
open unitInterval
variable {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

 

omit [IsTopologicalGroup Q] in
theorem simplyConnected_quotient [SimplyConnectedSpace G] (π : G →* Q)
    (hπ : Surjective π) (hπc : Continuous π) [PathConnectedSpace π.ker]
    (hsec : ∀ x : Q, ∃ U : Set Q, IsOpen U ∧ x ∈ U ∧ ∃ s : Q → G,
      ContinuousOn s U ∧ ∀ y ∈ U, π (s y) = y) : SimplyConnectedSpace Q := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨hπ.pathConnectedSpace hπc,?_⟩
  intro x γ
  obtain ⟨e,rfl⟩ := hπ x
  obtain ⟨Γ,hΓπ,hΓ0⟩ := exists_path_lift π hsec γ.toContinuousMap e γ.source.symm
  have hΓ1 : π (Γ 1) = π e := (congrFun hΓπ 1).trans γ.target
  let v := (Γ 1)⁻¹ * e
  have hv : v ∈ π.ker := by simp only [MonoidHom.mem_ker, v, map_mul, map_inv, hΓ1, inv_mul_cancel]
  let κ := PathConnectedSpace.somePath (1 : π.ker) ⟨v,hv⟩
  let ζ : Path e e := {
    toFun := fun t => Γ t * (κ t : G)
    continuous_toFun := Γ.continuous.mul (continuous_subtype_val.comp κ.continuous)
    source' := by simp only [κ.source,hΓ0,OneMemClass.coe_one,mul_one]
    target' := by simp only [κ.target,v,mul_inv_cancel_left] }
  have hmap : ζ.map hπc = γ := by
    ext t
    change π (Γ t * (κ t : G)) = γ t
    rw [map_mul,show π (κ t : G) = 1 from (κ t).property,mul_one]
    exact congrFun hΓπ t
  have href : (Path.refl e).map hπc = Path.refl (π e) := by ext; rfl
  have hh := (SimplyConnectedSpace.paths_homotopic ζ (Path.refl e)).map ⟨π,hπc⟩
  simpa only [hmap,href] using hh

end RawQuotientTopology

namespace RawQuotientTopology
open unitInterval
variable {G Q V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [TopologicalSpace V]

 
lemma local_sections_of_chart (π : G →* Q) (hπ : Surjective π)
    (sectionFn : V → G) (hsectionFn : Continuous sectionFn) (q : OpenPartialHomeomorph V Q)
    (h1 : (1 : Q) ∈ q.target) (hq : (q : V → Q) = π ∘ sectionFn) :
    ∀ x : Q, ∃ U : Set Q, IsOpen U ∧ x ∈ U ∧ ∃ s : Q → G,
      ContinuousOn s U ∧ ∀ y ∈ U, π (s y) = y := by
  intro x
  obtain ⟨g,hg⟩ := hπ x
  let U := (fun y : Q => x⁻¹ * y) ⁻¹' q.target
  have hL : Continuous (fun y : Q => x⁻¹ * y) := continuous_const.mul continuous_id
  refine ⟨U,q.open_target.preimage hL,by simpa only [U,mem_preimage,inv_mul_cancel] using h1,
    (fun y => g * sectionFn (q.symm (x⁻¹ * y))),?_,?_⟩
  · exact continuousOn_const.mul (hsectionFn.comp_continuousOn
      (q.continuousOn_symm.comp hL.continuousOn (fun _ hy => hy)))
  · intro y hy
    have hright := q.right_inv hy
    change π (g * sectionFn (q.symm (x⁻¹ * y))) = y
    rw [map_mul,hg,← Function.comp_apply (f := π) (g := sectionFn),← hq,hright,mul_inv_cancel_left]

end RawQuotientTopology

namespace RawGroupSection

 
theorem simplyConnected_retract {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] (i : Y → X) (r : X → Y)
    (hi : Continuous i) (hr : Continuous r) (hri : LeftInverse r i) : SimplyConnectedSpace Y := by
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hri.surjective.pathConnectedSpace hr,?_⟩
  intro x y p q
  have hh := (SimplyConnectedSpace.paths_homotopic (p.map hi) (q.map hi)).map ⟨r,hr⟩
  have hh' := hh.pathCast (hri x).symm (hri y).symm
  convert hh' using 1 <;> ext t <;> exact (hri _).symm

variable {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  (π : G →* Q) (hπ : Continuous π) (s : Q → G) (hs : Continuous s)
  (hproj : ∀ q, π (s q) = q)

def fiberRetraction : G → π.ker := fun g => ⟨(s (π g))⁻¹ * g, by
  simp only [MonoidHom.mem_ker,map_mul,map_inv,hproj,inv_mul_cancel]⟩

omit [IsTopologicalGroup Q] in
include hπ hs in
lemma fiberRetraction_continuous : Continuous (fiberRetraction π s hproj) :=
  (((hs.comp hπ).inv).mul continuous_id).subtype_mk _

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace Q]
  [IsTopologicalGroup Q] in
lemma fiberRetraction_leftInverse (h1 : s 1 = 1) :
    LeftInverse (fiberRetraction π s hproj) (Subtype.val : π.ker → G) := by
  intro g
  apply Subtype.ext
  change (s (π (g : G)))⁻¹ * (g : G) = (g : G)
  rw [g.property,h1,inv_one,one_mul]

omit [IsTopologicalGroup Q] in
include hπ hs hproj in
 
theorem fiber_simplyConnected [SimplyConnectedSpace G] (h1 : s 1 = 1) :
    SimplyConnectedSpace π.ker :=
  simplyConnected_retract Subtype.val (fiberRetraction π s hproj) continuous_subtype_val
    (fiberRetraction_continuous π hπ s hs hproj) (fiberRetraction_leftInverse π s hproj h1)

 
def trivialization : Q × π.ker ≃ₜ G where
  toFun p := s p.1 * p.2
  invFun g := (π g, fiberRetraction π s hproj g)
  left_inv p := by
    apply Prod.ext
    · change π (s p.1 * p.2) = p.1
      rw [map_mul,hproj,p.2.property,mul_one]
    · apply Subtype.ext
      change (s (π (s p.1 * p.2)))⁻¹ * (s p.1 * p.2) = p.2
      rw [map_mul,hproj,p.2.property,mul_one,inv_mul_cancel_left]
  right_inv g := by
    change s (π g) * ((s (π g))⁻¹ * g) = g
    exact mul_inv_cancel_left _ _
  continuous_toFun := (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := hπ.prodMk (fiberRetraction_continuous π hπ s hs hproj)

end RawGroupSection

namespace RawGroupSection

def finAppendHomeomorph (m n : ℕ) : ((Fin m → ℝ) × (Fin n → ℝ)) ≃ₜ (Fin (m+n) → ℝ) where
  toFun p := Fin.append p.1 p.2
  invFun a := (a ∘ Fin.castAdd n,a ∘ Fin.natAdd m)
  left_inv p := by
    apply Prod.ext <;> funext i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  right_inv a := Fin.append_castAdd_natAdd
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left,Function.comp_def] using (continuous_apply j).comp continuous_fst
    · simpa only [Fin.append_right,Function.comp_def] using (continuous_apply j).comp continuous_snd
  continuous_invFun :=
    (continuous_pi (fun i => continuous_apply (Fin.castAdd n i))).prodMk
      (continuous_pi (fun i => continuous_apply (Fin.natAdd m i)))

end RawGroupSection
end

end OAI
