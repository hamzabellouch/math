import OAI.Analysis.AllenCahn.Resolvent

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff SchwartzMap LineDeriv
open Filter Topology

lemma resolventIterate_all_jets {n : ℕ} {α : Type*} {V F : Space n → ℝ}
    (hV : V.HasTemperateGrowth) (hV0 : ∀ x, 0 ≤ V x)
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 < F x)
    (f : α → 𝓢(Space n,ℝ)) (hf : ∀ a x, 0 ≤ f a x)
    (he : ∀ a x, f a x+V x*F x ≤ 2*F x-Laplacian.laplacian F x)
    {G W : ℝ} (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hg : ∀ x, ‖gradient F x‖ ≤ G*F x)
    (hL : ∀ x, |Laplacian.laplacian F x| ≤ W*F x)
    (hJV : ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet V l x| ≤ C)
    (hJf : ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ a x, |coordinateJet (f a) l x| ≤ C*F x) :
    ∀ k, JetControl (Set.univ : Set (α × ℕ)) (fun _ => F)
      (fun a => (resolventIterate V (f a.1) a.2 : Space n → ℝ)) k := by
  let u (a : α × ℕ) : Space n → ℝ := resolventIterate V (f a.1) a.2
  have hu (a : α × ℕ) (_ : a ∈ (Set.univ : Set (α × ℕ))) : ContDiff ℝ ∞ (u a) :=
    (resolventIterate V (f a.1) a.2).smooth ⊤
  have hus (a : α × ℕ) (_ : a ∈ (Set.univ : Set (α × ℕ))) : ContDiff ℝ ∞ (u (a.1,a.2+1)) := hu _ (Set.mem_univ _)
  have hs (a : α × ℕ) (_ : a ∈ (Set.univ : Set (α × ℕ))) := (f a.1).smooth ⊤
  have hv (_ : α × ℕ) (_ : True) := hV.1
  intro k
  induction k with
  | zero =>
    apply JetControl.of_zero (C := 1) zero_le_one
    intro a ha x
    rw [one_mul,abs_of_nonneg (resolventIterate_nonneg hV hV0 (hf a.1) a.2 x)]
    exact resolventIterate_comparison hV hV0 (smooth_C2 hF) (fun x => (hF0 x).le) (he a.1) a.2 x
  | succ k ih =>
    have his := ih.reindex (T := Set.univ) (fun a : α × ℕ => (a.1,a.2+1)) (fun _ _ => Set.mem_univ _)
    have hjv : JetControl (Set.univ : Set (α × ℕ)) (fun _ _ => 1) (fun _ => V) k := by
      intro l hl
      obtain ⟨C,hC,hCb⟩ := hJV l
      exact ⟨C,hC,fun _ _ x => by simpa using hCb x⟩
    have hjf : JetControl (Set.univ : Set (α × ℕ)) (fun _ => F) (fun a => (f a.1 : Space n → ℝ)) k := by
      intro l hl
      obtain ⟨C,hC,hCb⟩ := hJf l
      exact ⟨C,hC,fun a _ x => hCb a.1 x⟩
    let r (a : α × ℕ) (x : Space n) := 2*u (a.1,a.2+1) x-f a.1 x-V x*u a x
    have hr (a : α × ℕ) (_ : a ∈ (Set.univ : Set (α × ℕ))) : ContDiff ℝ ∞ (r a) :=
      ((contDiff_const.mul (hus a (Set.mem_univ _))).sub (hs a (Set.mem_univ _))).sub
        (hV.1.mul (hu a (Set.mem_univ _)))
    have hjr : JetControl (Set.univ : Set (α × ℕ)) (fun _ => F) r k :=
      ((his.const_mul hus 2).sub (fun a ha => contDiff_const.mul (hus a ha)) hs hjf).sub
        (fun a ha => (contDiff_const.mul (hus a ha)).sub (hs a ha))
        (fun a ha => hV.1.mul (hu a ha))
        (hjv.mul_bounded (fun _ _ => hV.1) hu (fun _ _ x => (hF0 x).le) ih)
    have H : JetControl (Set.univ : Set (α × ℕ)) (fun _ => F)
        (fun a => u (a.1,a.2+1)) (k+1) := by
      apply JetControl.bootstrap hus hr (bc := fun _ _ _ => 0) (b := fun _ _ => 0)
        (fun _ _ _ => contDiff_const) (fun _ _ => smooth_C2 hF) (fun _ _ => hF0)
        (fun _ _ _ _ => by simp) (fun a _ x => ?_) (B := 0) le_rfl hG hW
        (fun _ _ _ => by simp) (fun _ _ => hg) (fun _ _ x => by simpa using hL x)
        (fun _ => JetControl.const _ 0 k) his hjr
      have HH := resolventIterate_equation hV (f a.1) a.2 x
      dsimp only [r,u]
      simp only [map_zero,sub_zero]
      linarith
    intro l hl
    obtain ⟨C,hC,hCb⟩ := H l hl
    refine ⟨C,hC,fun ⟨a,j⟩ _ x => ?_⟩
    cases j with
    | zero =>
      change |coordinateJet (fun _ => (0 : ℝ)) l x| ≤ C*F x
      rw [coordinateJet_zero, abs_zero]
      exact mul_nonneg hC (hF0 x).le
    | succ j => exact hCb (a,j) (Set.mem_univ _) x

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff SchwartzMap
open Filter Topology

def radialCutoffBase {n : ℕ} (x : Space n) : ℝ := Real.smoothTransition (2-‖x‖^2)

lemma radialCutoffBase_smooth (n : ℕ) : ContDiff ℝ ∞ (radialCutoffBase : Space n → ℝ) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.norm_sq ℝ))

lemma radialCutoffBase_compact (n : ℕ) : HasCompactSupport (radialCutoffBase : Space n → ℝ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space n) 2)
  intro x hx
  have hx' : 2 < ‖x‖ := by simpa using hx
  exact Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg x])

lemma coordinateJet_comp_smul {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (l : List (Fin n)) (x : Space n) :
    coordinateJet (fun x => f (c • x)) l x=c^l.length*coordinateJet f l (c • x) := by
  induction l generalizing x with
  | nil => simp [coordinateJet]
  | cons i l ih =>
    let A : Space n →L[ℝ] Space n := c • ContinuousLinearMap.id ℝ (Space n)
    have hA : ∀ y, A y=c • y := fun y => rfl
    have hd : Differentiable ℝ (coordinateJet f l) := (coordinateJet_smooth hf l).differentiable (by simp)
    have he : coordinateJet (fun x => f (c • x)) l = fun x => c^l.length*coordinateJet f l (A x) := funext ih
    change coordDeriv (coordinateJet (fun x => f (c • x)) l) i x = _
    rw [he]
    have HH := ((hd (A x)).hasFDerivAt.comp x A.hasFDerivAt).const_mul (c^l.length)
    change fderiv ℝ (fun x => c^l.length*coordinateJet f l (A x)) x (basis n i)=_
    simp only [Function.comp_def] at HH
    rw [HH.fderiv]
    simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,A,
      ContinuousLinearMap.id_apply,map_smul,List.length_cons,pow_succ,coordinateJet,coordDeriv]
    ring

def radialCutoffScale (j : ℕ) : ℝ := ((j : ℝ)+1)⁻¹

def radialCutoff {n : ℕ} (j : ℕ) (x : Space n) : ℝ :=
  radialCutoffBase (radialCutoffScale j • x)

lemma radialCutoffScale_pos (j : ℕ) : 0 < radialCutoffScale j := by
  dsimp [radialCutoffScale]; positivity

lemma radialCutoffScale_le_one (j : ℕ) : radialCutoffScale j ≤ 1 := by
  apply (inv_le_one₀ (by positivity : 0 < (j : ℝ)+1)).mpr
  simp

lemma radialCutoff_smooth {n : ℕ} (j : ℕ) : ContDiff ℝ ∞ (radialCutoff j : Space n → ℝ) := by
  change ContDiff ℝ ∞ (fun x : Space n => radialCutoffBase (radialCutoffScale j • x))
  exact (radialCutoffBase_smooth n).comp (by fun_prop)

lemma radialCutoff_bounds {n : ℕ} (j : ℕ) (x : Space n) :
    0 ≤ radialCutoff j x ∧ radialCutoff j x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

lemma radialCutoff_compact {n : ℕ} (j : ℕ) : HasCompactSupport (radialCutoff j : Space n → ℝ) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space n) (2*((j : ℝ)+1)))
  intro x hx
  have hx' : 2*((j : ℝ)+1) < ‖x‖ := by simpa using hx
  have hnorm : 2 < ‖radialCutoffScale j • x‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (radialCutoffScale_pos j)]
    dsimp [radialCutoffScale]
    rw [← div_eq_inv_mul]
    exact (lt_div_iff₀ (by positivity)).mpr hx'
  exact Real.smoothTransition.zero_of_nonpos (by nlinarith [norm_nonneg (radialCutoffScale j • x)])

lemma radialCutoff_mono {n : ℕ} (x : Space n) : Monotone (fun j => radialCutoff j x) := by
  intro j k hjk
  apply Real.smoothTransition.monotone
  have hq : radialCutoffScale k ≤ radialCutoffScale j := by
    apply inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
  have hnorm : ‖radialCutoffScale k • x‖ ≤ ‖radialCutoffScale j • x‖ := by
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (radialCutoffScale_pos k),abs_of_pos (radialCutoffScale_pos j)]
    exact mul_le_mul_of_nonneg_right hq (norm_nonneg x)
  nlinarith [norm_nonneg (radialCutoffScale k • x)]

lemma radialCutoff_eventually_one {n : ℕ} (x : Space n) : ∀ᶠ j : ℕ in atTop, radialCutoff j x=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with j hj
  have hnorm : ‖radialCutoffScale j • x‖ ≤ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (radialCutoffScale_pos j)]
    dsimp [radialCutoffScale]
    rw [← div_eq_inv_mul]
    apply (div_le_one (by positivity)).mpr
    have : (N : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  exact Real.smoothTransition.one_of_one_le (by nlinarith [norm_nonneg (radialCutoffScale j • x)])

lemma radialCutoff_isometry {n : ℕ} (J : Space n ≃ₗᵢ[ℝ] Space n) (j : ℕ) (x : Space n) :
    radialCutoff j (J x)=radialCutoff j x := by
  simp only [radialCutoff,radialCutoffBase,norm_smul,J.norm_map]

lemma radialCutoff_jets (n : ℕ) (l : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, |coordinateJet (radialCutoff j) l x| ≤ C := by
  let f : 𝓢(Space n,ℝ) := (radialCutoffBase_compact n).toSchwartzMap (radialCutoffBase_smooth n)
  obtain ⟨C,hC,hCb⟩ := schwartz_jets_bounded f l
  refine ⟨C,hC,fun j x => ?_⟩
  change |coordinateJet (fun y : Space n => radialCutoffBase (radialCutoffScale j • y)) l x| ≤ C
  rw [coordinateJet_comp_smul (radialCutoffBase_smooth n),abs_mul,
    abs_of_nonneg (pow_nonneg (radialCutoffScale_pos j).le _)]
  apply (mul_le_mul_of_nonneg_left (hCb (radialCutoffScale j • x))
    (pow_nonneg (radialCutoffScale_pos j).le _)).trans
  apply mul_le_of_le_one_left hC
  exact pow_le_one₀ (radialCutoffScale_pos j).le (radialCutoffScale_le_one j)

def cutSource {n : ℕ} {S : Space n → ℝ} (hS : ContDiff ℝ ∞ S) (j : ℕ) : 𝓢(Space n,ℝ) :=
  ((radialCutoff_compact j).mul_right).toSchwartzMap ((radialCutoff_smooth j).mul hS)

lemma cutSource_apply {n : ℕ} {S : Space n → ℝ} (hS : ContDiff ℝ ∞ S) (j : ℕ) (x : Space n) :
    cutSource hS j x=radialCutoff j x*S x := rfl

lemma cutSource_nonneg {n : ℕ} {S : Space n → ℝ} (hS : ContDiff ℝ ∞ S) (hS0 : ∀ x, 0 ≤ S x) :
    ∀ j x, 0 ≤ cutSource hS j x := fun j x => mul_nonneg (radialCutoff_bounds j x).1 (hS0 x)

lemma cutSource_le {n : ℕ} {S : Space n → ℝ} (hS : ContDiff ℝ ∞ S) (hS0 : ∀ x, 0 ≤ S x) :
    ∀ j x, cutSource hS j x ≤ S x := fun j x => mul_le_of_le_one_left (hS0 x) (radialCutoff_bounds j x).2

lemma cutSource_mono {n : ℕ} {S : Space n → ℝ} (hS : ContDiff ℝ ∞ S) (hS0 : ∀ x, 0 ≤ S x)
    {j k : ℕ} (hjk : j ≤ k) : ∀ x, cutSource hS j x ≤ cutSource hS k x := by
  intro x
  exact mul_le_mul_of_nonneg_right (radialCutoff_mono x hjk) (hS0 x)

lemma cutSource_tendsto {n : ℕ} {S : Space n → ℝ} (hS : ContDiff ℝ ∞ S) (x : Space n) :
    Tendsto (fun j => cutSource hS j x) atTop (𝓝 (S x)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [radialCutoff_eventually_one x] with j hj
  simp only [cutSource_apply,hj,one_mul]

lemma cutSource_isometry {n : ℕ} {S : Space n → ℝ} (hS : ContDiff ℝ ∞ S)
    (J : Space n ≃ₗᵢ[ℝ] Space n) (hJS : ∀ x, S (J x)=S x) (j : ℕ) (x : Space n) :
    cutSource hS j (J x)=cutSource hS j x := by
  simp only [cutSource_apply,radialCutoff_isometry,hJS]

lemma cutSource_jets {n : ℕ} {S F : Space n → ℝ} (hS : ContDiff ℝ ∞ S)
    (hF : ∀ x, 0 ≤ F x)
    (hJS : ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet S l x| ≤ C*F x) :
    ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ j x, |coordinateJet (cutSource hS j) l x| ≤ C*F x := by
  intro l
  have h1 : JetControl (Set.univ : Set ℕ) (fun _ (_ : Space n) => 1) radialCutoff l.length := by
    intro L hL
    obtain ⟨C,hC,hCb⟩ := radialCutoff_jets n L
    exact ⟨C,hC,fun j _ x => by simpa using hCb j x⟩
  have h2 : JetControl (Set.univ : Set ℕ) (fun _ => F) (fun _ => S) l.length := by
    intro L hL
    obtain ⟨C,hC,hCb⟩ := hJS L
    exact ⟨C,hC,fun _ _ => hCb⟩
  obtain ⟨C,hC,hCb⟩ := (h1.mul_bounded (fun j _ => radialCutoff_smooth j)
    (fun _ _ => hS) (fun _ _ => hF) h2) l le_rfl
  exact ⟨C,hC,fun j x => hCb j (Set.mem_univ _) x⟩

theorem even_source_exhaustion {n : ℕ} {V S F : Space n → ℝ}
    (hV : V.HasTemperateGrowth) (hV0 : ∀ x, 0 ≤ V x)
    (hS : ContDiff ℝ ∞ S) (hS0 : ∀ x, 0 ≤ S x)
    (hF : ContDiff ℝ ∞ F) (hF0 : ∀ x, 0 < F x)
    (he : ∀ x, -Laplacian.laplacian F x+(2-V x)*F x=S x)
    {G W : ℝ} (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hg : ∀ x, ‖gradient F x‖ ≤ G*F x)
    (hL : ∀ x, |Laplacian.laplacian F x| ≤ W*F x)
    (hJV : ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet V l x| ≤ C)
    (hJS : ∀ l, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet S l x| ≤ C*F x)
    (J : Space n ≃ₗᵢ[ℝ] Space n) (hJV' : ∀ x, V (J x)=V x) (hJS' : ∀ x, S (J x)=S x) :
    ∃ E : Space n → ℝ, ContDiff ℝ ∞ E ∧ (∀ x, 0 ≤ E x) ∧ (∀ x, E x ≤ F x) ∧
      (∀ x, -Laplacian.laplacian E x+(2-V x)*E x=S x) ∧ (∀ x, E (J x)=E x) := by
  let f := cutSource hS
  let u (j k : ℕ) : Space n → ℝ := resolventIterate V (f j) k
  have hu (j k) : ContDiff ℝ ∞ (u j k) := (resolventIterate V (f j) k).smooth ⊤
  have hfs (j x) : f j x+V x*F x ≤ 2*F x-Laplacian.laplacian F x := by
    dsimp only [f]
    have H := cutSource_le hS hS0 j x
    nlinarith [he x]
  have hpos (j k x) : 0 ≤ u j k x := resolventIterate_nonneg hV hV0 (cutSource_nonneg hS hS0 j) k x
  have hbound (j k x) : u j k x ≤ F x :=
    resolventIterate_comparison hV hV0 (smooth_C2 hF) (fun x => (hF0 x).le) (hfs j) k x
  have hmono {j k : ℕ} (hjk : j ≤ k) (m x) : u j m x ≤ u k m x :=
    resolventIterate_mono_source hV hV0 (cutSource_mono hS hS0 hjk) m x
  have hmonok (j x) : Monotone (fun k => u j k x) :=
    resolventIterate_mono_index hV hV0 (cutSource_nonneg hS hS0 j) x
  have hall := resolventIterate_all_jets hV hV0 hF hF0 f (cutSource_nonneg hS hS0)
    hfs hG hW hg hL hJV (cutSource_jets hS (fun x => (hF0 x).le) hJS)
  have hlocal (l : List (Fin n)) (R : ℝ) (hR : 0 < R) : ∃ M : ℝ, 0 ≤ M ∧
      ∀ j x, ‖x‖ ≤ R → |coordinateJet (u j (j+1)) l x| ≤ M := by
    obtain ⟨C,hC,hCb⟩ := hall l.length l le_rfl
    obtain ⟨z,hz,hmax⟩ := (isCompact_closedBall (0 : Space n) R).exists_isMaxOn
      ⟨0,by simpa using hR.le⟩ hF.continuous.continuousOn
    refine ⟨C*F z,mul_nonneg hC (hF0 z).le,fun j x hx => ?_⟩
    exact (hCb (j,j+1) (Set.mem_univ _) x).trans
      (mul_le_mul_of_nonneg_left (hmax (by simpa using hx)) hC)
  obtain ⟨a,g,ha,hgSmooth,hjet⟩ := all_jet_subsequence (ι := Unit)
    (f := fun j _ => u j (j+1)) (fun j _ => hu j (j+1)) (fun _ => hlocal)
  let E := g ()
  have hE : ContDiff ℝ ∞ E := hgSmooth ()
  have hj (l : List (Fin n)) (x : Space n) :
      Tendsto (fun j => coordinateJet (u (a j) (a j+1)) l x) atTop (𝓝 (coordinateJet E l x)) :=
    (hjet () l).tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)
  have hbase (x : Space n) : Tendsto (fun j => u (a j) (a j+1) x) atTop (𝓝 (E x)) := hj [] x
  have hprev (x : Space n) : Tendsto (fun j => u (a j) (a j) x) atTop (𝓝 (E x)) := by
    have hm : Monotone (fun j => u j j x) := by
      intro j k hjk
      exact (hmono hjk j x).trans (hmonok k x hjk)
    have hbo : BddAbove (Set.range (fun j => u j j x)) := ⟨F x,fun y ⟨j,hj⟩ => hj ▸ hbound j j x⟩
    have H := tendsto_atTop_ciSup hm hbo
    have H' : Tendsto (fun j => u j (j+1) x) atTop (𝓝 (⨆ j, u j j x)) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le H (H.comp (tendsto_add_atTop_nat 1))
      · intro j; exact hmonok j x (Nat.le_succ j)
      · intro j; exact hmono (Nat.le_succ j) (j+1) x
    have heq : (⨆ j, u j j x)=E x := tendsto_nhds_unique (H'.comp ha.tendsto_atTop) (hbase x)
    rw [← heq]
    exact H.comp ha.tendsto_atTop
  refine ⟨E,hE,fun x => ?_,fun x => ?_,fun x => ?_,fun x => ?_⟩
  · exact ge_of_tendsto (hbase x) (Filter.Eventually.of_forall (fun j => hpos (a j) (a j+1) x))
  · exact le_of_tendsto (hbase x) (Filter.Eventually.of_forall (fun j => hbound (a j) (a j+1) x))
  · have HL : Tendsto (fun j => Laplacian.laplacian (u (a j) (a j+1)) x) atTop
        (𝓝 (Laplacian.laplacian E x)) := by
      have H := tendsto_finsetSum Finset.univ (fun i _ => hj [i,i] x)
      simpa only [laplacian_eq_sum_coordDeriv (smooth_C2 hE),
        laplacian_eq_sum_coordDeriv (smooth_C2 (hu _ _)),coordinateJet] using H
    have H₁ := ((hbase x).const_mul 2).sub HL
    have H₂ := ((cutSource_tendsto hS x).comp ha.tendsto_atTop).add ((hprev x).const_mul (V x))
    have heq : (fun j => 2*u (a j) (a j+1) x-Laplacian.laplacian (u (a j) (a j+1)) x) =
        fun j => f (a j) x+V x*u (a j) (a j) x := funext (fun j => resolventIterate_equation hV (f (a j)) (a j) x)
    rw [heq] at H₁
    have HH := tendsto_nhds_unique H₁ H₂
    linarith
  · have hi (j) : u (a j) (a j+1) (J x)=u (a j) (a j+1) x :=
      resolventIterate_isometry hV J hJV' (cutSource_isometry hS J hJS' (a j)) (a j+1) x
    exact tendsto_nhds_unique (hbase (J x)) ((hbase x).congr (fun j => (hi j).symm))

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff Polynomial
open Filter Topology

lemma SmallDefectConverges.relative_D_jets {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (l : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet (g (some none)) l x| ≤ C*g (some none) x := by
  obtain ⟨C,hC,hb⟩ := (positiveAC_all_jets n l.length).2.2.1 l le_rfl
  refine ⟨C,hC,fun x => ?_⟩
  apply le_of_tendsto_of_tendsto ((hg.at_D l x).abs) ((hg.at_D [] x).const_mul C)
  filter_upwards [] with j
  rw [abs_mul,abs_of_pos (inv_pos.mpr ((hv j).2.2.2 0))]
  calc _ ≤ (diffuseDefect (v j) 0)⁻¹*(C*diffuseDefect (v j) x) :=
      mul_le_mul_of_nonneg_left (hb (v j) (hv j) x) (inv_pos.mpr ((hv j).2.2.2 0)).le
    _ = _ := by simp only [coordinateJet]; ring

lemma SmallDefectConverges.relative_T_jets {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (a b : Fin n) (l : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet (g (some (some (a,b)))) l x| ≤
      C*Real.sqrt (g (some none) x) := by
  obtain ⟨C,hC,hb⟩ := (positiveAC_all_jets n l.length).2.2.2 a b l le_rfl
  refine ⟨C,hC,fun x => ?_⟩
  have hs : (coordinateJet (g (some (some (a,b)))) l x)^2 ≤ C^2*g (some none) x := by
    apply le_of_tendsto_of_tendsto ((hg.at_T a b l x).pow 2) ((hg.at_D [] x).const_mul (C^2))
    filter_upwards [] with j
    have H := pow_le_pow_left₀ (abs_nonneg _) (hb (v j) (hv j) x) 2
    rw [sq_abs,mul_pow,defectRoot_sq ((hv j).2.2.2 x)] at H
    rw [mul_pow, inv_pow,defectRoot_sq ((hv j).2.2.2 0)]
    calc _ ≤ (diffuseDefect (v j) 0)⁻¹*(C^2*diffuseDefect (v j) x) :=
        mul_le_mul_of_nonneg_left H (inv_pos.mpr ((hv j).2.2.2 0)).le
      _ = _ := by simp only [coordinateJet]; ring
  have hd := (hg.positive hv).2 x
  have hsq := Real.sq_sqrt hd.le
  have hnon := mul_nonneg hC (Real.sqrt_nonneg (g (some none) x))
  nlinarith [sq_abs (coordinateJet (g (some (some (a,b)))) l x)]

lemma profile_comp_inner_coord {n : ℕ} (ν : Space n) (i : Fin n) (x : Space n) :
    coordDeriv (fun z => profile (inner ℝ ν z)) i x =
      (inner ℝ ν (basis n i)/Real.sqrt 2)*profileWeight (inner ℝ ν x) := by
  have H := (profile_hasDerivAt (inner ℝ ν x)).comp_hasFDerivAt x (innerSL ℝ ν).hasFDerivAt
  change fderiv ℝ (fun z : Space n => profile (inner ℝ ν z)) x (basis n i)=_
  simp only [Function.comp_def] at H
  rw [H.fderiv]
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply]
  ring

lemma weight_comp_inner_coord {n : ℕ} (ν : Space n) (i : Fin n) (x : Space n) :
    coordDeriv (fun z => profileWeight (inner ℝ ν z)) i x =
      (-Real.sqrt 2*inner ℝ ν (basis n i))*profile (inner ℝ ν x)*profileWeight (inner ℝ ν x) := by
  have H := (profileWeight_hasDerivAt (inner ℝ ν x)).comp_hasFDerivAt x (innerSL ℝ ν).hasFDerivAt
  change fderiv ℝ (fun z : Space n => profileWeight (inner ℝ ν z)) x (basis n i)=_
  simp only [Function.comp_def] at H
  rw [H.fderiv]
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply]
  ring

end DeGiorgi
end

end OAI
