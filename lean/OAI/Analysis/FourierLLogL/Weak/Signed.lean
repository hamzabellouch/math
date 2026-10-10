import OAI.Analysis.FourierLLogL.Weak.Cover

noncomputable section
open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology

namespace OAI

namespace FourierLLogL.Weak
open Real
open scoped Classical
variable {f : Torus → ℂ} {n : ℕ} {w : ℝ}

def drag (z : Torus) (f : Torus → ℂ) (x : Torus) := f (z+x)

lemma translated_bill (f : Torus → ℂ) (z : Torus) :
    modBill (drag z f) w = modBill f w := by
  unfold modBill drag circleMeasure
  exact integral_add_left_eq_self (fun x : Torus => priceΦ (‖f x‖/w)) z

lemma translated_in (z : Torus) (h : inside f) : inside (drag z f) := by
  have HE := flow z
  have hi (g : Torus → ℂ) (h : Integrable g law) :
      Integrable (fun i => g (z+i)) law := (HE.integrable_comp_of_integrable (g:=g) h)
  refine ⟨⟨(hi f h.1.integrable).1,?_⟩,?_⟩
  exact HE.integrable_comp_of_integrable (g:=Young f) (show Integrable (Young f) law from h.1.2)
  rw [translated_bill]; exact h.2

lemma fourier_drag (k : ℤ) (x y : Torus) :
    fourier k (x+y)=fourier k x * fourier k y := by
  simp_rw [fourier_apply,smul_add,AddCircle.toCircle_add,Circle.coe_mul]

lemma translated_sum (z x : Torus) (f : Torus→ℂ) (N : ℕ) :
    symmetricPartialSum (drag z f) N x=symmetricPartialSum f N (z+x) := by
  have HE (k : ℤ) : fourierCoeff (drag z f) k = fourier k z * fourierCoeff f k := by
    simp_rw [fourierCoeff_eq_integral]
    let w := fun i => f i*fourier (-k) i
    have H (i) : drag z f i*fourier (-k) i=fourier k z * w (z+i) := by
      unfold drag w; rw [fourier_drag]
      have HS : fourier k z*fourier (-k) z=1 := by
        rw [← fourier_add]; simp
      calc
        _ = f (z+i)*fourier (-k) i * (fourier k z*fourier (-k) z) := by rw [HS]; ring
        _ = _ := by ring
    change (∫ i,_ ∂law) = fourier k z* ∫ i,w i ∂law
    simp_rw [H]; rw [integral_const_mul]
    unfold law circleMeasure; rw [integral_add_left_eq_self]
  unfold symmetricPartialSum
  exact Finset.sum_congr rfl fun i _ => by rw [HE, fourier_drag]; ring

abbrev Toss (n : ℕ) := Fin n → Bool

def mark (b : Bool) : ℂ := if b then -1 else 1
lemma norm_mark (b) : ‖mark b‖=1 := by cases b <;> norm_num [mark]
def slate (f : Torus→ℂ) (z : Fin n → Torus) (c : Toss n) :=
    fun (x : Torus) => (n:ℝ)⁻¹ • ∑ i, mark (c i)*drag (z i) f x

lemma family_in (f : Torus→ℂ) (z : Fin n→ Torus) (h : inside f) (hp : 0 < n)
    (c : Toss n) : inside (slate f z c) := by
  let : NeZero n := ⟨hp.ne'⟩
  let g (i : Fin n) x := mark (c i)*drag (z i) f x
  have H (i : Fin n) : inside (g i) := by
    have he := translated_in (z i) h
    refine ⟨mem_dilate _ he.1,?_⟩
    have HE : modBill (g i) 1=modBill (drag (z i) f) 1 := by
      unfold modBill g; simp only [norm_mul,norm_mark,one_mul]
    rw [HE]; exact he.2
  have HZ := sum_inside g H
  simp only [Fintype.card_fin] at HZ
  exact HZ

lemma symm_sum (s : Finset (Fin n)) (f : Fin n→Torus→ℂ)
    (h : ∀ i, Integrable (f i) circleMeasure) (k : ℕ) (x : Torus) :
    symmetricPartialSum (fun y => ∑ i∈s,f i y) k x=
      ∑ i∈s,symmetricPartialSum (f i) k x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    change symmetricPartialSum (f i+(fun y => ∑ j∈t,f j y)) _ _=_
    rw [symmetricPartialSum_add (h i) (integrable_finsetSum _ (fun i _ => h i)),ih]

lemma slate_sum (z : Fin n→Torus) (x : Torus) (h : inside f) (k : ℕ) (c : Toss n) :
    symmetricPartialSum (slate f z c) k x =
      (((n:ℝ)⁻¹:ℝ):ℂ)*∑ i,mark (c i)*symmetricPartialSum f k (z i+x) := by
  have HF (i : Fin n) : Integrable (drag (z i) f) circleMeasure :=
    (translated_in _ h).1.integrable
  let g (i : Fin n) (x) := mark (c i)*drag (z i) f x
  unfold slate
  simp_rw [Complex.real_smul]
  rw [symmetricPartialSum_const_mul,symm_sum _ g (fun i => (HF i).const_mul _)]
  unfold g
  simp_rw [symmetricPartialSum_const_mul,translated_sum]

def switch (i : Fin n) : Toss n ≃ Toss n :=
    let w (f : Toss n) (x : Fin n) := if x=i then !f i else f x
    let he : LeftInverse w w := fun c => by
      funext p; by_cases h : p=i <;> simp [w,h]
    ⟨w,w,he,he⟩

lemma flipsum_bill (g : Fin n → ℂ) (j : Fin n) (c : Toss n) :
    let f (c : Toss n) := ∑ i,mark (c i)*g i
    f c-f (switch j c)=2*mark (c j)*g j := by
  intro f; unfold f
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · cases h : c j <;> simp only [switch,Equiv.coe_fn_mk,ite_true,h] <;>
      norm_num [mark] <;> ring
  · intro b _ h
    simp [switch, h]
  simp

def appears (s : Set Torus) (x : Torus) := if x∈s then (1:ℝ) else 0
lemma signed_window (h : inside f) (p : ℝ) (hp : 0 < p)
    (z : Fin n → Torus) (hn : 0 < n) (x : Torus) :
    let q := fun c : Toss n => cloudSet (slate f z c) (p/n)
    (Fintype.card (Toss n):ℝ)*appears (spread (cloudSet f p) z) x ≤
      2 * ∑ c,appears (q c) x := by
  intro q
  have HH (c) : 0 ≤ appears (q c) x := by unfold appears; split <;> norm_num
  by_cases hM : x∈spread (cloudSet f p) z
  · rw [show appears _ x=1 from ite_eq_left hM,mul_one]
    obtain ⟨j,hb⟩ := hM
    obtain ⟨N,hX⟩ := (cloudy f hp.le (z j+x)).mp hb
    let B := fun i : Fin n => symmetricPartialSum f N (z i+x)
    let C (c : Toss n) := ∑ i,mark (c i)*B i
    let a := (n:ℝ)
    have ha : 0 < a := by unfold a; positivity
    have HE (c : Toss n) (hx : p < ‖C c‖) : appears (q c) x=1 := by
      refine ite_eq_left ?_
      refine (cloudy _ (show 0 ≤ p/a by positivity) x).2 ⟨N,?_⟩
      rw [slate_sum z x h, norm_mul,Complex.norm_real,Real.norm_eq_abs]
      change p/a < |a⁻¹| * ‖C c‖
      rw [abs_of_pos (inv_pos.2 ha),←div_eq_inv_mul]
      exact (div_lt_div_iff_of_pos_right ha).mpr hx
    have HQ (c : Toss n) : 1 ≤ appears (q c) x + appears (q (switch j c)) x := by
      by_cases hh : p < ‖C c‖
      · rw [HE c hh]; linarith [HH (switch j c)]
      have Ht := norm_sub_le (C c) (C (switch j c))
      have hJ : ‖C c-C (switch j c)‖ = 2*‖B j‖ := by
        rw [show C c-C (switch j c)=_ from flipsum_bill B j c]
        simp only [norm_mul,norm_mark]; norm_num
      rw [hJ] at Ht
      change p < ‖B j‖ at hX
      have hs : p < ‖C (switch j c)‖ := by linarith
      rw [HE _ hs]; linarith [HH c]
    let A (c : Toss n) := appears (q c) x
    have H : ∑ _c : Toss n,(1:ℝ) ≤ ∑ c,(A c+A (switch j c)) :=
      Finset.sum_le_sum fun i _ => HQ i
    have Hv : ∑ c,A (switch j c) = ∑ c,A c :=
      Fintype.sum_equiv (switch j) _ _ fun _ => rfl
    rw [Finset.sum_add_distrib,Hv] at H; simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_univ] at H
    change _ ≤ 2*∑ c,A c; linarith
  · rw [show appears _ x=0 from ite_eq_right hM,mul_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => HH i)

lemma occurs_meas (S : Set Torus) (h : MeasurableSet S) :
    Integrable (appears S) law ∧ (∫ x,appears S x ∂law)=law.real S := by
  rw [show appears S=S.indicator (fun _ => (1:ℝ)) by
    funext x; by_cases h : x∈S <;> simp [appears,h]]
  refine ⟨(integrable_const _).indicator h,?_⟩; rw [integral_indicator h]; simp

lemma circle_bill (hp : GoodBound) :
    ∃ v : ℝ, 0 < v ∧ ∀ f : Torus→ℂ, inside f →
      ∀ p : ℝ, 0 < p → p*law.real (cloudSet f p) ≤ v := by
  obtain ⟨L,hL,hF⟩ := median_budget hp
  refine ⟨4*L,by positivity,?_⟩
  intro f h p hp
  let S := cloudSet f p
  have hS := cloud_meas f p
  rcases eq_or_lt_of_le (show 0 ≤ law.real S from measureReal_nonneg) with hr|hr
  · change _*law.real S ≤ _
    rw [←hr,mul_zero]; positivity
  obtain ⟨n,hn,z,hz,hv⟩ := clouds_fill S hS hr
  let m := (n:ℝ)
  have he : 0 < m := by unfold m; positivity
  suffices H : p/m ≤ L by
    change p*law.real S ≤ _
    rw [div_le_iff₀ he] at H
    change m*law.real S ≤ _ at hv
    nlinarith
  by_contra! H
  let q (c : Toss n) := cloudSet (slate f z c) (p/m)
  let k := (Fintype.card (Toss n) : ℝ)
  have HH (c : Toss n) : law.real (q c) ≤ 1/16 := by
    apply le_trans _ (hF _ (family_in f z h hn c))
    refine measureReal_mono ?_ (by finiteness)
    intro x hx
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal H.le) hx
  let b := spread S z
  have hB := occurs_meas b (spread_meas S z hS)
  have hQ (c) := occurs_meas (q c) (cloud_meas _ _)
  have HE : k*law.real b ≤ 2*∑ c,law.real (q c) := by
    rw [← hB.2,←integral_const_mul]
    simp_rw [← (hQ _).2]
    rw [← integral_finsetSum _ (fun i _ => (hQ i).1),
      ← integral_const_mul]
    apply integral_mono (hB.1.const_mul _) ((integrable_finsetSum _ fun i _ => (hQ i).1).const_mul _)
    exact signed_window h p hp z hn
  have Hx : ∑ c,law.real (q c) ≤ k*(1/16) := by
    calc
      _ ≤ ∑ c : Toss n, (1/16:ℝ) := Finset.sum_le_sum fun i _ => HH i
      _ = _ := by simp [k]
  have HE' : 0 < k := by unfold k; positivity
  change 1/2 ≤ law.real b at hz
  nlinarith

end FourierLLogL.Weak

end OAI
