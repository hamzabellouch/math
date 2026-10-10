import OAI.Geometry.Convex.GeneralMahler.Profiles

namespace OAI
/-! §07 stable Laplace moments. Define using the translated Gaussian variable
on (x,∞). -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal
namespace GeneralMahler.SCal
open Profile Layers
def Lpn (n:Nat) (x y:ℝ):= phi y*((y-x)^n / phi x)
def Ymk (n:Nat) (x:ℝ):= ∫ y in Ioi x,Lpn n x y
lemma lp_r (n:Nat) (x:ℝ): rapid (Lpn n x) := by
  have h : PolyBound (fun y:ℝ=>(y-x)^n/phi x) := by
    simp only [div_eq_mul_inv]; exact ((PolyBound.id.sub (PolyBound.const _)).pow n).mul (PolyBound.const _)
  exact rapid_phi.product h
lemma lp_i (n:Nat) (x:ℝ) : Integrable (Lpn n x) := by
  have h : Continuous (Lpn n x) := by
    unfold Lpn; exact c_phi.mul (Continuous.div_const (by fun_prop) _)
  exact (lp_r n x).integrable_real h.measurable
lemma Ymp (n:Nat) (x:ℝ): 0 < Ymk n x := by
  have hh (y) (hy:x<y) : 0< Lpn n x y := mul_pos (phi_pos _)
    (div_pos (pow_pos (sub_pos.mpr hy) n) (phi_pos x))
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ (lp_i n x).integrableOn).mpr
  · apply lt_of_lt_of_le (isOpen_Ioi.measure_pos volume (Set.nonempty_Ioi (a:=x)))
    apply measure_mono
    exact fun y hy=> ⟨(hh y hy).ne',hy⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy; exact (hh y hy).le
lemma Ym0 : Ymk 0=Y := by
  ext x; unfold Ymk Lpn Y
  simp_rw [pow_zero, mul_one_div,integral_div,int_Ioi]
lemma Hd0 (x y:ℝ) : HasDerivAt (Lpn 0 x) (-x*Lpn 0 x y-Lpn 1 x y) y := by
  have he : Lpn 0 x=fun y=> phi y/phi x := by unfold Lpn; ext y; ring
  rw [he]
  convert (d_phi y).div_const (phi x) using 1
  all_goals first| rfl| (unfold Lpn; dsimp only; ring)
lemma Hdn (x y:ℝ) (n:Nat) : HasDerivAt (Lpn (n+1) x)
    (((n+1:Nat):ℝ)*Lpn n x y - x*Lpn (n+1) x y-Lpn (n+2) x y) y := by
  have h:= (d_phi y).mul ((((hasDerivAt_id' y).sub_const x).pow (n+1)).div_const (phi x))
  convert h using 1
  all_goals first | rfl | skip
  unfold Lpn
  push_cast; simp [pow_succ]; ring
lemma R0 (x:ℝ) : x*Ymk 0 x+Ymk 1 x=1 := by
  let f:=Lpn 0 x
  have hi : Integrable (fun y=> -x*f y-Lpn 1 x y):=
    ((lp_i 0 x).const_mul _).sub (lp_i 1 x)
  have he:= integral_Ioi_of_hasDerivAt_of_tendsto'
    (a:=x) (fun y _=>Hd0 x y) hi.integrableOn (lp_r 0 x).tail_limit
  rw [integral_sub (((lp_i 0 x).integrableOn).const_mul _) (lp_i 1 x).integrableOn,
    integral_const_mul] at he
  rw [show Lpn 0 x x=1 from by unfold Lpn; field_simp [(phi_pos x).ne']] at he
  unfold Ymk; linarith
lemma Rn (x:ℝ) (n:Nat) : x*Ymk (n+1) x+Ymk (n+2) x = ((n+1:Nat):ℝ)*Ymk n x := by
  have hi : Integrable (fun y=> ((n+1:Nat):ℝ)*Lpn n x y-x*Lpn (n+1) x y) :=
    ((lp_i _ x).const_mul _).sub ((lp_i _ x).const_mul _)
  have he:= integral_Ioi_of_hasDerivAt_of_tendsto'
    (a:=x) (fun y _=>Hdn x y n) (hi.sub (lp_i _ x)).integrableOn (lp_r _ x).tail_limit
  rw [integral_sub hi.integrableOn (lp_i _ x).integrableOn,integral_sub (((lp_i _ x).integrableOn).const_mul _)
    (((lp_i _ x).integrableOn).const_mul _),integral_const_mul, integral_const_mul] at he
  rw [show Lpn (n+1) x x=0 from by simp [Lpn]] at he
  unfold Ymk; linarith
lemma DYmk0 (x:ℝ) : HasDerivAt (Ymk 0) (-(Ymk 1 x)) x := by
  have hh:=R0 x
  rw [Ym0] at *
  convert dY x using 1; unfold Yd; linarith
lemma DYmk (x:ℝ) (n:Nat): HasDerivAt (Ymk n) (-(Ymk (n+1) x)) x := by
  have h0:=DYmk0 x
  have he :∀ n:Nat, HasDerivAt (Ymk n) (-(Ymk (n+1) x)) x ∧
      HasDerivAt (Ymk (n+1)) (-(Ymk (n+2) x)) x := by
    intro n; induction n with
    | zero=>
      have hh : Ymk 1=fun x=> 1-x*Ymk 0 x:= funext fun x=>by linarith [R0 x]
      refine ⟨h0,?_⟩
      change HasDerivAt (Ymk 1) _ x; rw [hh]
      convert (hasDerivAt_const x 1).sub ((hasDerivAt_id' x).mul h0) using 1
      have hi:=Rn x 0; norm_num at *; linarith
    | succ n ih=>
      refine ⟨ih.2,?_⟩
      have hh : Ymk (n+2)=fun x=> ((n+1:Nat):ℝ)*Ymk n x-x*Ymk (n+1) x :=
        funext fun x=>by linarith [Rn x n]
      change HasDerivAt (Ymk (n+2)) _ x
      rw [hh]
      convert (ih.1.const_mul ((n+1:Nat):ℝ)).sub ((hasDerivAt_id' x).mul ih.2) using 1
      have hi:=Rn x (n+1)
      push_cast at *; linarith
  exact (he n).1
lemma Yanti (n:Nat): StrictAnti (Ymk n) :=
  strictAnti_of_deriv_neg fun x=> by rw [(DYmk x n).deriv]; linarith [Ymp (n+1) x]

-- continued fraction
def cRat (n:Nat) (x:ℝ):= Ymk (n+1) x/Ymk n x
lemma cRp (n:Nat) (x:ℝ): 0<cRat n x := div_pos (Ymp ..) (Ymp ..)
lemma cfBase (x:ℝ) : (x+cRat 0 x)* Ymk 0 x=1 := by
  unfold cRat; rw [add_mul,div_mul_cancel₀ _ (Ymp 0 x).ne']; apply R0
lemma cfIter (n:Nat) (x:ℝ): cRat n x * (x+cRat (n+1) x)=((n+1:Nat):ℝ) := by
  unfold cRat
  have h1:=(Ymp n x).ne'
  have h2:=(Ymp (n+1) x).ne'
  field_simp
  have he:=Rn x n; push_cast at *; nlinarith

end GeneralMahler.SCal

end

end OAI
