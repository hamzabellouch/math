import OAI.GroupTheory.PolycyclicRecognition.Analysis.LocalProfileAffinity

namespace OAI

/-! # Local affine height formulas agree on a connected open domain -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter
open scoped Topology

theorem affine_parameters_eq_on_open
    {W Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {U : Set W} (hU : IsOpen U) (hne : U.Nonempty)
    (A B : W →L[ℝ] Z) (b c : Z)
    (heq : ∀ x ∈ U, A x + b = B x + c) : A = B ∧ b = c := by
  obtain ⟨x, hx⟩ := hne
  have hfg : (fun y => A y + b) =ᶠ[𝓝 x] (fun y => B y + c) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heq y hy
  have hA := (A.hasFDerivAt (x := x)).add_const b
  have hB := (B.hasFDerivAt (x := x)).add_const c
  have hAB : A = B := (hA.congr_of_eventuallyEq hfg.symm).unique hB
  refine ⟨hAB, ?_⟩
  have h := heq x hx
  rw [hAB] at h
  exact add_left_cancel h

theorem exists_global_affine_of_local
    {G W Z L : Type*} [TopologicalSpace G]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (π : G → W) (hπ : IsOpenMap π) (A : L → W →L[ℝ] Z) (f : G → Z)
    {U : Set G} (hconn : IsPreconnected U) (hne : U.Nonempty)
    (hlocal : ∀ x ∈ U, ∃ N : Set G, IsOpen N ∧ x ∈ N ∧ N ⊆ U ∧
      ∃ l b, ∀ y ∈ N, f y = A l (π y) + b) :
    ∃ l b, ∀ x ∈ U, f x = A l (π x) + b := by
  classical
  have hchoices (x : U) := hlocal x.val x.property
  choose N hNo hNx hNU l b he using hchoices
  let C : U → (W →L[ℝ] Z) × Z := fun x => (A (l x), b x)
  have hC : IsLocallyConstant C := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro x
    have hnear : ∀ᶠ y : U in 𝓝 x, y.val ∈ N x :=
      continuous_subtype_val.continuousAt.tendsto.eventually ((hNo x).mem_nhds (hNx x))
    filter_upwards [hnear] with y hy
    have ho : IsOpen (π '' (N y ∩ N x)) := hπ _ ((hNo y).inter (hNo x))
    have hn : (π '' (N y ∩ N x)).Nonempty := ⟨π y, y, ⟨hNx y, hy⟩, rfl⟩
    have hsame := affine_parameters_eq_on_open ho hn (A (l y)) (A (l x)) (b y) (b x) (by
      rintro z ⟨g, hg, rfl⟩
      exact (he y g hg.1).symm.trans (he x g hg.2))
    exact Prod.ext hsame.1 hsame.2
  let : PreconnectedSpace U := Subtype.preconnectedSpace hconn
  obtain ⟨x, hx⟩ := hne
  let x₀ : U := ⟨x, hx⟩
  refine ⟨l x₀, b x₀, ?_⟩
  intro y hy
  let y₀ : U := ⟨y, hy⟩
  have hsame := hC.apply_eq_of_preconnectedSpace y₀ x₀
  have hlin : A (l y₀) = A (l x₀) := congrArg Prod.fst hsame
  have hoff : b y₀ = b x₀ := congrArg Prod.snd hsame
  have hyformula := he y₀ y (hNx y₀)
  rw [hlin, hoff] at hyformula
  exact hyformula

end PolycyclicRecognition

end

end OAI
