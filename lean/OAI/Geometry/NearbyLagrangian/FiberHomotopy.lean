import Mathlib
import OAI.Geometry.NearbyLagrangian.StandardNegative
import OAI.Geometry.NearbyLagrangian.VerticalChanges
import OAI.Geometry.NearbyLagrangian.NegativeEquivalence

namespace OAI

/-! Fiberwise equivalences and homotopy invariance of negative fibrations. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes
open ContinuousMap
open scoped Topology
variable {B E F G : Type*} [TopologicalSpace B] [TopologicalSpace E]
  [TopologicalSpace F] [TopologicalSpace G]

namespace FiberwiseHomotopyEquiv

def refl (p : C(E,B)) : FiberwiseHomotopyEquiv p p where
  toFun := .id E
  invFun := .id E
  toFun_over _ := rfl
  invFun_over _ := rfl
  left := .refl (.id E)
  right := .refl (.id E)
  left_over _ _ := rfl
  right_over _ _ := rfl

def symm {p : C(E,B)} {q : C(F,B)} (e : FiberwiseHomotopyEquiv p q) :
    FiberwiseHomotopyEquiv q p where
  toFun := e.invFun
  invFun := e.toFun
  toFun_over := e.invFun_over
  invFun_over := e.toFun_over
  left := e.right
  right := e.left
  left_over := e.right_over
  right_over := e.left_over

lemma trans_over {p : C(E,B)} {f g h : C(E,E)}
    (H : f.Homotopy g) (K : g.Homotopy h)
    (hH : ∀ t x, p (H (t,x)) = p x) (hK : ∀ t x, p (K (t,x)) = p x) :
    ∀ t x, p (H.trans K (t,x)) = p x := by
  intro t x
  rw [Homotopy.trans_apply]
  split_ifs
  · exact hH _ _
  · exact hK _ _

def trans {p : C(E,B)} {q : C(F,B)} {r : C(G,B)}
    (e : FiberwiseHomotopyEquiv p q) (f : FiberwiseHomotopyEquiv q r) :
    FiberwiseHomotopyEquiv p r := by
  let T := f.toFun.comp e.toFun
  let I := e.invFun.comp f.invFun
  let L : (I.comp T).Homotopy (e.invFun.comp e.toFun) :=
    { toFun := fun z => e.invFun (f.left (z.1,e.toFun z.2))
      continuous_toFun := e.invFun.continuous.comp (f.left.continuous_toFun.comp
        (continuous_fst.prodMk (e.toFun.continuous.comp continuous_snd)))
      map_zero_left := by intro x; simp [I,T]
      map_one_left := by intro x; simp }
  let R : (T.comp I).Homotopy (f.toFun.comp f.invFun) :=
    { toFun := fun z => f.toFun (e.right (z.1,f.invFun z.2))
      continuous_toFun := f.toFun.continuous.comp (e.right.continuous_toFun.comp
        (continuous_fst.prodMk (f.invFun.continuous.comp continuous_snd)))
      map_zero_left := by intro x; simp [I,T]
      map_one_left := by intro x; simp }
  exact
    { toFun := T
      invFun := I
      toFun_over := fun x => (f.toFun_over _).trans (e.toFun_over x)
      invFun_over := fun x => (e.invFun_over _).trans (f.invFun_over x)
      left := L.trans e.left
      right := R.trans f.right
      left_over := trans_over L e.left (fun t x => by
        change p (e.invFun (f.left (t,e.toFun x))) = p x
        rw [e.invFun_over, f.left_over, e.toFun_over]) e.left_over
      right_over := trans_over R f.right (fun t x => by
        change r (f.toFun (e.right (t,f.invFun x))) = r x
        rw [f.toFun_over, e.right_over, f.invFun_over]) f.right_over }

end FiberwiseHomotopyEquiv
end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes
open Set Metric
open scoped Topology
variable {B : Type*} [TopologicalSpace B]

def negativeTotalInHomeomorph {k l : ℕ} (a : C(B,Tube k l)) :
    NegativeTotal a ≃ₜ NegativeIn {w : Euclidean (k+l) | ‖w‖ = 1}
      (fun p : B × Euclidean (k+l) => (a p.1).val p.2) where
  toFun x := ⟨(x.val.1,x.val.2.val), unitSphere_norm x.val.2,x.property⟩
  invFun x := ⟨(x.val.1,⟨x.val.2,by
    simpa only [mem_sphere,dist_zero_right,Set.mem_ofPred_eq] using x.property.1⟩),x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def FiberwiseHomotopyEquiv.ofNegativeIn {k l : ℕ} {a b : C(B,Tube k l)}
    (h : FiberwiseHomotopyEquiv
      (negativeInProjection {w : Euclidean (k+l) | ‖w‖ = 1}
        (fun p : B × Euclidean (k+l) => (a p.1).val p.2))
      (negativeInProjection {w : Euclidean (k+l) | ‖w‖ = 1}
        (fun p : B × Euclidean (k+l) => (b p.1).val p.2))) :
    FiberwiseHomotopyEquiv (negativeProjection a) (negativeProjection b) :=
  ((h.precomposeHomeomorph (p:=negativeProjection a) (negativeTotalInHomeomorph a)
    (fun _ => rfl)).symm.precomposeHomeomorph (p:=negativeProjection b)
      (negativeTotalInHomeomorph b) (fun _ => rfl)).symm

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter
open scoped Topology ContDiff Manifold InnerProductSpace
variable {W V B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold 𝓘(ℝ,V) ∞ B] [T2Space B] [CompactSpace B]

lemma norm_fderiv_gradient (f : RegularHomogeneous W) (w : W) :
    ‖fderiv ℝ f w‖ = ‖gradient f w‖ := by
  rw [← toDual_gradient]
  exact (InnerProductSpace.toDual ℝ W).norm_map _

omit [FiniteDimensional ℝ V] [T2Space B] in

theorem smooth_negative_of_approx (f : C(B,RegularHomogeneous W))
    {g₀ : B → W → ℝ} (hg₀ : ∀ b, ContDiff ℝ 1 (g₀ b))
    (hh₀ : ∀ b (r:ℝ), 0 < r → ∀ x, g₀ b (r • x) = r^2 * g₀ b x)
    (hs₀ : ∀ p : B × W, p.2 ≠ 0 →
      ContMDiffAt (𝓘(ℝ,V).prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) ∞ (Function.uncurry g₀) p)
    (hv₀ : Continuous (Function.uncurry g₀))
    (hd₀ : Continuous (fun p : B × W => fderiv ℝ (g₀ p.1) p.2))
    {c ε : ℝ} (hc : 0 < c) (hε : 0 ≤ ε) (hεc : ε ≤ c/128)
    (hm : ∀ b x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ (f b) x‖)
    (he₀ : ∀ b x, ‖x‖ = 1 → |g₀ b x-f b x| ≤ ε ∧
      ‖fderiv ℝ (g₀ b) x-fderiv ℝ (f b) x‖ ≤ ε) :
    ∃ g : C(B,RegularHomogeneous W), f.Homotopic g ∧ SmoothFamily (E:=V) g ∧
      Nonempty (FiberwiseHomotopyEquiv
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f p.1 p.2))
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => g p.1 p.2))) ∧
      ∀ b x, g b x = g₀ b x := by
  have hsmall : ε < c := by linarith
  obtain ⟨g,hH,hg⟩ := exists_family_blend f hg₀ hh₀ hv₀ hd₀ hc hm
    (fun b x hx => ((he₀ b x hx).2).trans_lt hsmall)
  have heq (b : B) : (g b : W → ℝ) = g₀ b := funext (hg b)
  have hs : SmoothFamily (E:=V) g := by
    have heq' : (fun p : B × W => g p.1 p.2) = Function.uncurry g₀ :=
      funext (fun p => hg p.1 p.2)
    unfold SmoothFamily
    rw [heq']
    exact hs₀
  have hclose : ∀ b x, ‖x‖ = 1 → |f b x-g b x| ≤ ε ∧
      ‖fderiv ℝ (f b) x-fderiv ℝ (g b) x‖ ≤ ε := by
    intro b x hx
    rw [hg b x,heq b,abs_sub_comm,norm_sub_rev]
    exact he₀ b x hx
  have hgrad (b : B) (x : W) (hx : ‖x‖ = 1) : c/2 ≤ ‖gradient (g b) x‖ := by
    rw [← norm_fderiv_gradient]
    have hnorm := norm_le_norm_add_norm_sub (fderiv ℝ (g b) x) (fderiv ℝ (f b) x)
    rw [norm_sub_rev] at hnorm
    have h := (hclose b x hx).2
    have hlow := hm b x hx
    linarith
  exact ⟨g,hH,hs,close_negative_family_equiv hs (half_pos hc) hε (by linarith)
    hgrad (fun b x hx => (hclose b x hx).1) (fun b x hx => (hclose b x hx).2),hg⟩

theorem exists_smooth_negative_equiv [Nontrivial W] (f : C(B,RegularHomogeneous W)) :
    ∃ g : C(B,RegularHomogeneous W), f.Homotopic g ∧ SmoothFamily (E:=V) g ∧
      Nonempty (FiberwiseHomotopyEquiv
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f p.1 p.2))
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => g p.1 p.2))) := by
  cases isEmpty_or_nonempty B with
  | inl h =>
    exact ⟨f,.refl f,fun p _ => isEmptyElim p.1,⟨.refl _⟩⟩
  | inr h =>
    obtain ⟨c,C,hc,_,hb⟩ := uniform_gradient_bounds f.continuous
    have hm (b : B) (w : W) (hw : ‖w‖ = 1) : c ≤ ‖fderiv ℝ (f b) w‖ := by
      rw [norm_fderiv_gradient]
      simpa only [hw,mul_one] using (hb b w).1
    obtain ⟨g₀,hg₀,_,hh₀,hs₀,hv₀,hd₀,he₀⟩ :=
      exists_smooth_family_approx (I:=𝓘(ℝ,V)) f.continuous (by positivity : 0 < c/128)
    obtain ⟨g,hH,hs,hN,_⟩ := smooth_negative_of_approx (ε:=c/128) f hg₀ hh₀ hs₀ hv₀ hd₀ hc
      (by positivity) le_rfl hm (fun b x hx => by simpa only [Real.norm_eq_abs] using he₀ b x hx)
    exact ⟨g,hH,hs,hN⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter
open scoped Topology ContDiff Manifold
variable {A B V W : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [CompactSpace B]

theorem eventually_uniform_jet_close (f : C(A × B,RegularHomogeneous W))
    (t₀ : A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ b w, ‖w‖ = 1 →
      |f (t,b) w-f (t₀,b) w| ≤ ε ∧
      ‖fderiv ℝ (f (t,b)) w-fderiv ℝ (f (t₀,b)) w‖ ≤ ε := by
  let S := Metric.sphere (0:W) 1
  have h₁ : Continuous (fun p : A × (B × S) => (f (p.1,p.2.1), (p.2.2:W))) :=
    (f.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have h₀ : Continuous (fun p : A × (B × S) => (f (t₀,p.2.1), (p.2.2:W))) :=
    (f.continuous.comp (continuous_const.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hval := ((continuous_eval.comp h₁).sub (continuous_eval.comp h₀)).abs
  have hder := ((continuous_fderiv_eval.comp h₁).sub
    (continuous_fderiv_eval.comp h₀)).norm
  have hev : ∀ᶠ t in 𝓝 t₀, ∀ y : B × S,
      |f (t,y.1) y.2-f (t₀,y.1) y.2| < ε ∧
      ‖fderiv ℝ (f (t,y.1)) y.2-fderiv ℝ (f (t₀,y.1)) y.2‖ < ε := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (X:=A) (Y:=B × S) (x₀:=t₀) (P:=fun t y =>
        |f (t,y.1) y.2-f (t₀,y.1) y.2| < ε ∧
        ‖fderiv ℝ (f (t,y.1)) y.2-fderiv ℝ (f (t₀,y.1)) y.2‖ < ε) ?_
    · simpa only [Set.mem_univ,forall_const] using h
    · intro y _
      have hv : ∀ᶠ p in 𝓝 (t₀,y), |f (p.1,p.2.1) p.2.2-f (t₀,p.2.1) p.2.2| < ε :=
        (isOpen_lt hval continuous_const).mem_nhds (by simpa using hε)
      have hd : ∀ᶠ p in 𝓝 (t₀,y),
          ‖fderiv ℝ (f (p.1,p.2.1)) p.2.2-fderiv ℝ (f (t₀,p.2.1)) p.2.2‖ < ε :=
        (isOpen_lt hder continuous_const).mem_nhds (by simpa using hε)
      exact hv.and hd
  filter_upwards [hev] with t ht
  intro b w hw
  let u : S := ⟨w, by change w ∈ Metric.sphere (0:W) 1; simpa only [Metric.mem_sphere,dist_zero_right] using hw⟩
  exact ⟨(ht (b,u)).1.le,(ht (b,u)).2.le⟩

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B] [T2Space B] [Nontrivial W]

include V in

theorem eventually_negative_equiv (f : C(A × B,RegularHomogeneous W)) (t₀ : A) :
    ∀ᶠ t in 𝓝 t₀, Nonempty (FiberwiseHomotopyEquiv
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f (t₀,p.1) p.2))
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f (t,p.1) p.2))) := by
  cases isEmpty_or_nonempty B with
  | inl h =>
    apply Filter.Eventually.of_forall
    intro t
    have heq : (fun p : B × W => f (t,p.1) p.2) = (fun p : B × W => f (t₀,p.1) p.2) :=
      funext (fun p => isEmptyElim p.1)
    rw [heq]
    exact ⟨.refl _⟩
  | inr h =>
    let f₀ : C(B,RegularHomogeneous W) :=
      ⟨fun b => f (t₀,b), f.continuous.comp (continuous_const.prodMk continuous_id)⟩
    obtain ⟨c,C,hc,_,hb⟩ := uniform_gradient_bounds f₀.continuous
    have hm (b : B) (w : W) (hw : ‖w‖ = 1) : c ≤ ‖fderiv ℝ (f₀ b) w‖ := by
      rw [norm_fderiv_gradient]
      simpa only [hw,mul_one] using (hb b w).1
    obtain ⟨g,_,hgs,hg⟩ := exists_smooth_homotopic_close_on_sphere (I:=𝓘(ℝ,V)) f₀ hc
      (by positivity : 0 < c/128) (by linarith : c/128 < c) hm
    have hggrad (b : B) (w : W) (hw : ‖w‖ = 1) : c/2 ≤ ‖gradient (g b) w‖ := by
      rw [← norm_fderiv_gradient]
      have hn := norm_le_norm_add_norm_sub (fderiv ℝ (g b) w) (fderiv ℝ (f₀ b) w)
      have he := (hg b w hw).2
      have hl := hm b w hw
      linarith
    have hcore := close_negative_family_equiv hgs (half_pos hc)
      (by positivity : 0 ≤ c/128) (by linarith : c/128 ≤ (c/2)/32) hggrad
      (fun b w hw => by rw [abs_sub_comm]; exact (hg b w hw).1)
      (fun b w hw => by rw [norm_sub_rev]; exact (hg b w hw).2)
    obtain ⟨e₀⟩ := hcore
    filter_upwards [eventually_uniform_jet_close f t₀ (by positivity : 0 < c/128)] with t ht
    have hv (b : B) (w : W) (hw : ‖w‖ = 1) : |f (t,b) w-g b w| ≤ c/64 := by
      have he := (ht b w hw).1
      have hg' := (hg b w hw).1
      have hn := abs_sub_le (f (t,b) w) (f₀ b w) (g b w)
      rw [abs_sub_comm (f₀ b w)] at hn
      change |f (t,b) w-f₀ b w| ≤ c/128 at he
      linarith
    have hd (b : B) (w : W) (hw : ‖w‖ = 1) :
        ‖fderiv ℝ (f (t,b)) w-fderiv ℝ (g b) w‖ ≤ c/64 := by
      have he := (ht b w hw).2
      have hg' := (hg b w hw).2
      have hn := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (f (t,b)) w) (fderiv ℝ (f₀ b) w) (fderiv ℝ (g b) w)
      rw [norm_sub_rev (fderiv ℝ (f₀ b) w)] at hn
      change ‖fderiv ℝ (f (t,b)) w-fderiv ℝ (f₀ b) w‖ ≤ c/128 at he
      linarith
    obtain ⟨e₁⟩ := close_negative_family_equiv hgs (half_pos hc)
      (by positivity : 0 ≤ c/64) (by linarith : c/64 ≤ (c/2)/32) hggrad hv hd
    exact ⟨e₀.trans e₁.symm⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set Filter ContinuousMap
open scoped Topology ContDiff Manifold
variable {A B V W : Type*} [TopologicalSpace A] [PreconnectedSpace A]
  [TopologicalSpace B] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]
  [T2Space B] [CompactSpace B] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Nontrivial W]

include V

theorem negative_equiv_connected (f : C(A × B,RegularHomogeneous W)) (t₀ t₁ : A) :
    Nonempty (FiberwiseHomotopyEquiv
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f (t₀,p.1) p.2))
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f (t₁,p.1) p.2))) := by
  let R : A → A → Prop := fun t s => Nonempty (FiberwiseHomotopyEquiv
    (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f (t,p.1) p.2))
    (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f (s,p.1) p.2)))
  have hloc (t : A) : ∀ᶠ s in 𝓝 t, R t s := eventually_negative_equiv (V:=V) f t
  let S : Set A := {t | R t₀ t}
  have ho : IsOpen S := isOpen_iff_mem_nhds.mpr fun t ht => by
    obtain ⟨e⟩ := ht
    filter_upwards [hloc t] with s hs
    obtain ⟨e'⟩ := hs
    exact ⟨e.trans e'⟩
  have hoc : IsOpen Sᶜ := isOpen_iff_mem_nhds.mpr fun t ht => by
    filter_upwards [hloc t] with s hs
    intro hst
    obtain ⟨e⟩ := hst
    obtain ⟨e'⟩ := hs
    exact ht ⟨e.trans e'.symm⟩
  have heq : S = univ := (show IsClopen S from ⟨isOpen_compl_iff.mp hoc,ho⟩).eq_univ
    ⟨t₀,⟨.refl _⟩⟩
  have ht : t₁ ∈ S := by rw [heq]; trivial
  exact ht

theorem negative_equiv_of_homotopic (f g : C(B,RegularHomogeneous W)) (h : f.Homotopic g) :
    Nonempty (FiberwiseHomotopyEquiv
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f p.1 p.2))
      (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => g p.1 p.2))) := by
  obtain ⟨H⟩ := h
  have he := negative_equiv_connected (V:=V) H.toContinuousMap (0:unitInterval) 1
  have h₀ : (fun p : B × W => H.toContinuousMap (0,p.1) p.2) =
      (fun p : B × W => f p.1 p.2) := by
    funext p
    exact congrArg (fun a : RegularHomogeneous W => a p.2) (H.apply_zero p.1)
  have h₁ : (fun p : B × W => H.toContinuousMap (1,p.1) p.2) =
      (fun p : B × W => g p.1 p.2) := by
    funext p
    exact congrArg (fun a : RegularHomogeneous W => a p.2) (H.apply_one p.1)
  rw [h₀,h₁] at he
  exact he

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes
open ContinuousMap
open scoped Topology ContDiff Manifold
variable {B V : Type*} [TopologicalSpace B] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]
  [T2Space B] [CompactSpace B]

theorem exists_smooth_tube {k l : ℕ} (hkl : 0 < k+l) (a : C(B,Tube k l)) :
    ∃ b : C(B,Tube k l), a.Homotopic b ∧
      RegularHomogeneous.SmoothFamily (E:=V) (fun x => (b x).val) ∧
      Nonempty (FiberwiseHomotopyEquiv (negativeProjection a) (negativeProjection b)) := by
  let : Nonempty (Fin (k+l)) := ⟨⟨0,hkl⟩⟩
  obtain ⟨g,hag,hgs,hneg⟩ :=
    RegularHomogeneous.exists_smooth_negative_equiv (V:=V) (tubeCoe.comp a)
  obtain ⟨b,hab,hb⟩ := lift_tube_homotopy a g hag
  have heq : tubeCoe.comp b = g := ContinuousMap.ext hb
  refine ⟨b,hab,?_,?_⟩
  · have heq' : (fun x => (b x).val) = (g : B → RegularHomogeneous (Euclidean (k+l))) :=
      funext hb
    rw [heq']
    exact hgs
  · rw [← heq] at hneg
    exact ⟨FiberwiseHomotopyEquiv.ofNegativeIn hneg.some⟩

include V in

theorem negative_equiv_tube_of_homotopic {k l : ℕ} (hkl : 0 < k+l)
    {a b : C(B,Tube k l)} (hab : a.Homotopic b) :
    Nonempty (FiberwiseHomotopyEquiv (negativeProjection a) (negativeProjection b)) := by
  let : Nonempty (Fin (k+l)) := ⟨⟨0,hkl⟩⟩
  obtain ⟨h⟩ := RegularHomogeneous.negative_equiv_of_homotopic (V:=V)
    (tubeCoe.comp a) (tubeCoe.comp b) ((Homotopic.refl tubeCoe).comp hab)
  exact ⟨FiberwiseHomotopyEquiv.ofNegativeIn h⟩

include V in
 theorem NegativeTrivial.of_homotopic {k l : ℕ} (hkl : 0 < k+l)
    {a b : C(B,Tube k l)} (ha : NegativeTrivial a) (hab : a.Homotopic b) :
    NegativeTrivial b := by
  obtain ⟨e⟩ := negative_equiv_tube_of_homotopic (V:=V) hkl hab
  exact ⟨e.symm.trans ha.some⟩

include V in
 theorem StableNegativeTrivial.of_homotopic {m : ℕ} (hm : 0 < m)
    {a b : C(B,Tube m m)} (ha : StableNegativeTrivial a) (hab : a.Homotopic b) :
    StableNegativeTrivial b := by
  obtain ⟨r,hr⟩ := ha
  exact ⟨r,hr.of_homotopic (V:=V) (by omega)
    ((Homotopic.refl (stabilizeFor m r)).comp hab)⟩

end NearbyLagrangian.Tubes

end

end OAI
