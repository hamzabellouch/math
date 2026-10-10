import OAI.Combinatorics.HadwigerCounterexample.SupportedPhaseLaws

namespace OAI

/-! # Offset Fourier Bounds -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix LinearMap Module Submodule Function Finset
variable {p : Shape} {n N r : ℕ} {T : Cov p N}

def chant (p : Shape) {n N} (Δ : UnitType p n N → Ambient p N) (S R : Party) :
    Wgt (UnitType p n N × UnitType p n N) :=
  fun x => wsign (tone p x.1 R (Δ x.2)+tone p x.2 S (Δ x.1))

variable {U V : Type} [AddCommGroup U] [AddCommGroup V] [Module F U] [Module F V]

def coupledB (A : U →ₗ[F] U →ₗ[F] F) (B : V →ₗ[F] V →ₗ[F] F) :
    U × V→ₗ[F] U × V→ₗ[F] F where
  toFun x := (A x.1).coprod (B x.2)
  map_add' x y := LinearMap.ext fun z => by
    simp only [Prod.fst_add,Prod.snd_add,map_add,LinearMap.add_apply,LinearMap.coprod_apply]
    abel
  map_smul' a x := LinearMap.ext fun z => by
    simp only [Prod.smul_fst,Prod.smul_snd,map_smul,RingHom.id_apply,LinearMap.smul_apply,
      LinearMap.coprod_apply,smul_add]

theorem coupledB_inj {A : U →ₗ[F] U →ₗ[F] F} {B : V →ₗ[F] V →ₗ[F] F}
    (ha : Injective A) (hb : Injective B) :
    Injective (coupledB A B) := by
  intro x y h
  apply Prod.ext
  · apply ha
    refine LinearMap.ext fun z => ?_
    have he : A x.1 z+B x.2 0=A y.1 z+B y.2 0 := LinearMap.congr_fun h (z,0)
    simpa only [map_zero,add_zero] using he
  apply hb
  refine LinearMap.ext fun z => ?_
  have he : A x.1 0+B x.2 z=A y.1 0+B y.2 z := LinearMap.congr_fun h (0,z)
  simpa only [map_zero,zero_add] using he

theorem tupleB_comm (p : Shape) (r : Place p→ℕ) (N : ℕ) (x y) :
    tupleB p r N x y=tupleB p r N y x := by
  rw [tupleB_val,tupleB_val]
  exact Finset.sum_congr rfl fun i _ => mpair_comm ..

namespace Bazaar
variable (s : Bazaar p n r T)

abbrev Sales (p : Shape) {N} (n r : ℕ) (T : Cov p N) :=
  Atlas p r T → Atlas p r T → UnitType p n N → Prop

def discard {s : Bazaar p n r T} (w : Wgt (UnitType p n N)) (C : Sales p n r T) :=
  pr (pairW w w) (fun x => ¬ C (s.ix x.1) (s.ix x.2) x.2)

set_option maxHeartbeats 800000 in
private theorem beat_one {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : SubLaw w) (M G : Atlas p r T)
    (S R : Party) (i : Bool) (C : UnitType p n N → Prop)
    (hA : ∀ x,mapW (s.chart w M) (s.bag M i) x ≤ loseA p N (cells M) 0)
    (hB : standard M → standard G → ∀ y,mapW (subW (s.chart w G) C)
      (s.pay M G i S) y ≤ prize p N (cells G)) :
    |avg (pairW (s.chart w M) (subW (s.chart w G) C)) (chant p Δ S R)| ≤ beat N := by
  classical
  let u := s.chart w M
  let v := subW (s.chart w G) C
  have hw : SubLaw u := subLaw_sub hv _
  have ht : SubLaw v := subLaw_sub (subLaw_sub hv _) _
  let y := avg (pairW u v) (chant p Δ S R)
  by_cases hy : y=0
  · change |y|≤_
    rw [hy, abs_zero]; exact (bp_pos _).le
  have h : ∃ x,pairW u v x ≠ 0 := by
    by_contra! he
    apply hy; unfold y avg; simp_rw [he]; simp
  obtain ⟨⟨x0,y0⟩,hx⟩ := h
  have hV x (hh : v x≠0) : s.chart w G x≠0 := left_ne_zero_of_mul hh
  have H (x : UnitType p n N) (hh : u x≠0) := s.active hl x hh
  have H' (x : UnitType p n N) (hh : v x≠0) := s.active hl x (hV x hh)
  let a (x) := (s.bag M i x,thermal p x R (src G))
  let b := s.pay M G i S
  let f (x : UnitType p n N) := wsign (tone p x R (edgeCost G))
  let g (x : UnitType p n N) := wsign (tone p x S (edgeCost M))
  let B := coupledB (tupleB p (breadth M) N) (tupleB p (breadth G) N)
  have hc :
      y=avg (pairW u v) (fun x => f x.1*g x.2*wsign (B (a x.1) (b x.2))) := by
    refine avg_congr fun ⟨x,y⟩ hh => ?_
    have h1 := ((H x (left_ne_zero_of_mul hh)).2.2 i).2
    have h2 := ((H' y (right_ne_zero_of_mul hh)).2.2 i).2
    unfold chant; dsimp only
    rw [h1,h2,tone_offset,tone_offset]
    unfold f g
    rw [←wsign_add,←wsign_add]
    apply congrArg wsign
    change _=_+(tupleB p (breadth M) N _ _+tupleB p (breadth G) N _ _)
    rw [tupleB_comm p (breadth G) N (s.bag G i y)]
    dsimp only [coupledB,b,pay,a]
    simp only [LinearMap.fst_apply,LinearMap.snd_apply]
    abel
  let D := Batch M N × Batch G N
  have ha (x : D) : mapW u a x ≤ loseA p N (cells M) 0 := by
    refine (pr_mono hw.nz (p:=fun y => a y=x) (q:=fun y => s.bag M i y=x.1)
      (fun y h => ?_)).trans (hA x.1)
    exact congrArg Prod.fst h
  have hb (x : D) : mapW v b x ≤ prize p N (cells G) :=
    hB ((H x0 (left_ne_zero_of_mul hx)).2.1) ((H' y0 (right_ne_zero_of_mul hx)).2.1) x
  have he := walsh_weighted B
    (coupledB_inj (tupleB_inj ..) (tupleB_inj ..)) u v hw ht a b f g (fun x => by simp [f])
    (fun x => by simp [g]) ha hb
  have hi : y^2 ≤ beat N^2 := by
    rw [hc]
    refine he.trans ?_
    let F := Batch M N
    let G' := Batch G N
    unfold num
    rw [card_space,dim,finrank_prod]
    have hf : finrank HadwigerCounterexample.F F=N*cells M := tuple_dim
    have hg : finrank HadwigerCounterexample.F G'=N*cells G := tuple_dim
    rw [hf,hg,loseA,prize,beat,←bp_add,←bp_add,pow_two,←bp_add]
    apply le_of_eq; push_cast; ring_nf
  change |y|≤_
  exact le_of_pow_le_pow_left₀ (show 2 ≠ (0:ℕ) by decide) (bp_pos _).le
    (sq_abs y ▸ hi)

set_option maxHeartbeats 800000 in
theorem beat_mix {w : Wgt (UnitType p n N)} {Δ}
    (hl : s.opened Δ w) (hv : IsLaw w) (S R : Party) (i : Bool) (C : Sales p n r T)
    (hA : ∀ M x,mapW (s.chart w M) (s.bag M i) x ≤ loseA p N (cells M) 0)
    (hB : ∀ M G,standard M → standard G → ∀ y,mapW (subW (s.chart w G) (C M G))
      (s.pay M G i S) y ≤ prize p N (cells G))
    (ht : num (Atlas p r T) ≤ bp (0.002*N)) :
    |pitch p Δ w S R| ≤ discard (s:=s) w C + bp (-0.24*N) := by
  classical
  let V := pairW w w
  let F := chant p Δ S R
  let P := fun x : (UnitType p n N)×_ => C (s.ix x.1) (s.ix x.2) x.2
  let g := fun x => ind (P x)*F x
  let f := fun x => ind (¬P x)*F x
  let μ := s.chart w
  let W := fun M G => subW (μ G) (C M G)
  have hn x : 0≤ V x := (pairW_law hv hv).nz x
  have he x : F x=f x+ g x := by
    unfold f g
    by_cases h : P x <;> simp [h]
  have hf : |avg V f| ≤ discard (s:=s) w C := by
    refine (abs_avg_le hn).trans_eq ?_
    unfold discard pr
    refine avg_congr (fun x _ => ?_)
    rw [show f x= _*_ from rfl, abs_mul, abs_of_nonneg (ind_nonneg (¬P x))]
    simp [F,P,chant]
  have hg :
      avg V g=∑ M : Atlas p r T,∑ G : Atlas p r T, avg (pairW (μ M) (W M G)) F := by
    let U (M G : Atlas p r T) (x : UnitType p n N × UnitType p n N) :=
      ind (s.ix x.1=M)*ind (s.ix x.2=G)*ind (C M G x.2)*F x
    have hu (M G : Atlas p r T) :
        avg (pairW (μ M) (W M G)) F=avg V (U M G) := by
      unfold avg
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold U W μ V pairW chart subW; ring
    simp_rw [hu,← avg_sum]
    refine avg_congr fun x _ => ?_
    rw [Finset.sum_eq_single (s.ix x.1)]
    · rw [Finset.sum_eq_single (s.ix x.2)]
      · simp only [U,ind_true,one_mul]; rfl
      · intro j _ hj; simp [U,ind_zero hj.symm]
      simp
    · intro j _ hj; simp [U,ind_zero hj.symm]
    simp
  have hh : |avg V g| ≤ bp (-0.24*N) := by
    rw [hg]; apply le_trans (Finset.abs_sum_le_sum_abs ..)
    let J := num (Atlas p r T)
    have hz (M : Atlas p r T) :
        |∑ G : Atlas p r T, avg (pairW (μ M) (W M G)) F|≤ J*beat N := by
      refine (Finset.abs_sum_le_sum_abs ..).trans
        ((Finset.sum_le_sum (fun i' _ =>
          beat_one s hl hv.sub M i' S R i (C M i') (hA M) (hB M i'))).trans_eq ?_)
      simp only [J,Finset.sum_const, Finset.card_univ,nsmul_eq_mul,num]
    calc ∑ M : Atlas p r T,|∑ G : Atlas p r T,avg (pairW (μ M) (W M G)) F|
      _ ≤ ∑ _ : Atlas p r T,J*beat N := Finset.sum_le_sum fun M _ => hz M
      _ = J*J*beat N := by simp [J,mul_assoc,num]
      _ ≤ bp (0.002*N)*bp (0.002*N)*beat N := mul_le_mul_of_nonneg_right
        (mul_self_le_mul_self (Nat.cast_nonneg _ : 0≤J) ht) (bp_pos _).le
      _ ≤ bp (-0.24*N) := by
        unfold beat; rw [← bp_add,← bp_add]; apply bp_le; linarith [(Nat.cast_nonneg N : 0≤(N:ℝ))]
  change |avg V F|≤ _
  rw [show F=(fun x => f x+g x) from funext he,avg_add]
  exact (abs_add_le ..).trans (add_le_add hf hh)

end Bazaar
end HadwigerCounterexample

end

end OAI
