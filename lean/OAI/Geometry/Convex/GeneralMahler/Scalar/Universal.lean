import OAI.Geometry.Convex.GeneralMahler.Scalar.Tail.PassTail
import OAI.Geometry.Convex.GeneralMahler.Scalar.NodesTbl
import OAI.Geometry.Convex.GeneralMahler.Scalar.Regular

namespace OAI
/-! Propagate and combine the finite/infinite and reflected ranges. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Grid Tag Profile CJet Cert Cert.IV
def NG:=By Nodes.passesAt 0 721
variable {X:ℕ}

lemma NG.good (h:NG) (n:ℕ) (hi:n ≤ 720): NodeTrue n (Nodes.A n)∧(n<720 → pass n=true ∧ ∀ x∈Icc (nd n) (nd (n+1)), K.act x ≤ gv (Nodes.A n).mx) := line_good n (Nodes.A n) (h n (by omega) (by omega))

lemma nd0: nd 0=0:=by norm_num [nd]
lemma nd_m:StrictMono nd := by intro i j h; unfold nd; gcongr
lemma find_cell (n i:ℕ) (h:i<n) {x:ℝ} (hx:x∈Icc (nd i) (nd n)):
    ∃ j:ℕ,i ≤ j∧ j<n ∧ x∈Icc (nd j) (nd (j+1)) := by
  induction n with
  | zero=> omega
  | succ n ih=>
    by_cases hj:nd n≤ x
    · exact ⟨n,by omega,by omega,hj,hx.2⟩
    have hi:i<n := by
      have hv: nd i < nd n := lt_of_le_of_lt hx.1 (lt_of_not_ge hj)
      exact nd_m.lt_iff_lt.mp hv
    obtain ⟨j,hj,hz,hg⟩:=ih hi ⟨hx.1,(lt_of_not_ge hj).le⟩
    exact ⟨j,hj,by omega,hg⟩

lemma x720 : (658/10:ℝ) ≤ xs (nd 720) := by
  have hi:=mle (mbd 658000) (pGa 720).X (by decide +kernel)
  convert hi using 1; norm_num
lemma x225 : xs (nd 225) ≤ (5:ℝ) := by
  have hi:=mle (pGa 225).X (mbd 50000) (by decide +kernel)
  convert hi using 1; norm_num
lemma x280 : xs (nd 280)≤ (686/100:ℝ) := by
  have hi:=mle (pGa 280).X (mbd 68600) (by decide +kernel)
  convert hi using 1; norm_num

lemma find_tail {x:ℝ} (hh:nd 720 ≤ x): ∃ y, Tail.y0≤ y∧ xs x=Tail.XX y := by
  have hi:= x_mono.monotone hh
  have hp : 64≤xs x := by linarith [x720]
  exact ⟨Real.log (xs x), Real.log_le_log (by norm_num) hp, (Real.exp_log (by linarith)).symm⟩

lemma rp_th (h:NG) {x:ℝ} (hx:0≤ x):R.act x∈rng R := by
  rcases le_total x (nd 720) with he|he
  · obtain ⟨n,_,hn,hu⟩:=find_cell 720 0 (by decide) ⟨nd0.symm ▸ hx,he⟩
    exact cell_R (((h.good n hn.le).2 hn).1) hu
  obtain ⟨y,hy,hi⟩:=find_tail he
  exact Tail.rad_tail hy hi
lemma rp_bound (h:NG) (x:ℝ):5/100≤ rad x := by
  obtain ⟨t,ht⟩:=ontoX x
  rw [← ht]
  have hh:= rp_th h (abs_nonneg t)
  have he : R.act |t| = rad (xs t) := by
    rcases le_total t 0 with he|he
    · rw [abs_of_nonpos he]; exact lift_ref Reven _
    rw [abs_of_nonneg he]; rfl
  rw [he] at hh
  have hv:=(mem_band _ _ _).mp hh
  norm_num at hv; linarith [hv.1]
lemma hrq (h:NG): RadH:=fun x=>by linarith [rp_bound h x]
lemma hqt (h:NG):TestF qu:=q_reg (rp_bound h)

lemma stage_size (n:ℕ) (h:n<720): stage n≤8∧(panel (stage n)).lo≤n∧ n<(panel (stage n)).hi := by
  unfold stage; split_ifs <;> norm_num [panel,pan] <;> omega

-- whenever past lower index r. returns cell n and panel contains x
lemma Propagate (h:NG) {x:ℝ} {r:ℕ} (hr:r<720) (hu:nd r ≤ x) :
    ∃ n:ℕ,r ≤ n∧ n<720∧
      nd (panel (stage n)).lo ≤ x∧ ((panel (stage n)).hi<720 → x ≤ nd (panel (stage n)).hi) ∧
      passR n (fun t=>t.act x) := by
  rcases le_total x (nd 720) with he|he
  · obtain ⟨n,hn,hx,hc⟩:= find_cell 720 r hr ⟨hu,he⟩
    have hs:= stage_size n hx
    exact ⟨n,hn,hx,(nd_m.monotone hs.2.1).trans hc.1,
      fun _=> hc.2.trans (nd_m.monotone (by omega)),
      cell_pass (((h.good n hx.le).2 hx).1) (hrq h) (hqt h) hc⟩
  obtain ⟨y,hy,hd⟩:= find_tail he
  refine ⟨719,by omega,by decide,(nd_m.monotone (by decide)).trans he,fun h=>?_,
    passes (fun i=>Tail.tag_tail hy hd (hrq h) (hqt h) i) Tail.tailCheck⟩
  norm_num [stage,panel,pan] at h

-- per-real argument assertion
lemma Sym_b (i:Tag)(h:i.odd=true): SubB (-(rng i)) (rng i) &&
    SubB (-(roff i)) (roff i) := by cases i <;> first| decide|simp [Tag.odd] at h
lemma mRange (h:NG) (x:ℝ) (i:Tag):i.act x∈rng i := by
  have hh:= abs_nonneg x
  obtain ⟨n,_,_,_,_,hg⟩:= Propagate h (r:=0) (by decide) (show nd 0≤|x| from nd0.symm ▸ hh)
  have he:=hg.gr i
  rcases le_total 0 x with hz|hz
  · simpa only [abs_of_nonneg hz] using he
  rw [abs_of_nonpos hz] at he
  rcases hb:i.odd with _|_
  · rw [Tag.TvEv (hqt h) hb] at he; exact he
  rw [Tag.TvOd (hqt h) hb] at he
  have ht:=Sym_b i hb; simp only [Bool.and_eq_true] at ht
  simpa only [neg_neg] using subB (mneg he) ht.1
lemma mOff (h:NG) (x:ℝ) (hx:nd 280 ≤ |x|) (i:Tag):i.act x∈roff i := by
  obtain ⟨n,hn,_,_,_,hg⟩:= Propagate h (by decide : 280 <720) hx
  have he:=hg.off hn i
  rcases le_total 0 x with hz|hz
  · simpa only [abs_of_nonneg hz] using he
  rw [abs_of_nonpos hz] at he
  rcases hb:i.odd with _|_
  · rw [Tag.TvEv (hqt h) hb] at he; exact he
  rw [Tag.TvOd (hqt h) hb] at he
  have ht:=Sym_b i hb; simp only [Bool.and_eq_true] at ht
  simpa only [neg_neg] using subB (mneg he) ht.2

lemma mFive (h:NG) (x:ℝ) (hx:5 ≤ |xs x|): Tag.Q.act x∈x5 := by
  have he:xs |x|=|xs x| := by
    rcases le_total 0 x with hz|hz
    · rw [abs_of_nonneg hz, abs_of_nonneg (by simpa [xs] using x_mono.monotone hz)]
    rw [abs_of_nonpos hz,x_neg,abs_of_nonpos (by simpa [xs] using x_mono.monotone hz)]
  have hh: nd 225 ≤|x|:= x_mono.le_iff_le.mp (x225.trans (he.symm ▸ hx))
  obtain ⟨n,hn,_,_,_,hg⟩:= Propagate h (by decide : 225 <720) hh
  have hf:=hg.five hn
  rcases le_total 0 x with hz|hz
  · simpa only [abs_of_nonneg hz] using hf
  rw [abs_of_nonpos hz,Tag.TvEv (hqt h) (show Q.odd=false by decide)] at hf; exact hf

lemma GlobalCorr (h:NG) (x:ℝ): Corr (fun i=>i.act x):= by
  have hh:=abs_nonneg x
  obtain ⟨n,_,_,_,_,hg⟩:= Propagate h (r:=0) (by decide) (show nd 0≤ |x| from nd0.symm ▸ hh)
  have hv:= hg.uu
  rcases le_total 0 x with hz|hz
  · simpa only [abs_of_nonneg hz] using hv
  have he (i:Tag)(he:i.odd=false):i.act (-x)=i.act x:= Tag.TvEv (hqt h) he x
  have ho (i:Tag)(he:i.odd=true):i.act (-x)= -i.act x:=Tag.TvOd (hqt h) he x
  rw [abs_of_nonpos hz] at hv
  unfold Corr Ucost at *
  dsimp only at *
  rw [he K (by rfl),he C (by rfl),he NK (by rfl),ho dK (by rfl),ho dC (by rfl)] at hv
  simp only [mul_neg,← neg_add, Even.neg_pow (show Even 2 by decide)] at hv
  exact hv
end GeneralMahler.SCal

end OAI
