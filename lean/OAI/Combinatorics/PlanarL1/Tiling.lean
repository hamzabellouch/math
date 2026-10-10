import OAI.Combinatorics.PlanarL1.Parameters
import OAI.Combinatorics.PlanarL1.Execution

namespace OAI


section

namespace PlanarL1
namespace Tiling
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The literal closed height bands. Adjacent bands share only their endpoint,
where every clipping proposal retains the old field. -/
def band (a q : ℝ) (k : ℤ) : Set ℝ := Set.Icc (q+k*a) (q+(k+1)*a)

lemma band_closed (a q : ℝ) (k : ℤ) : IsClosed (band a q k) := isClosed_Icc
lemma band_convex (a q : ℝ) (k : ℤ) : (band a q k).OrdConnected := Set.ordConnected_Icc

noncomputable def index (a q h : ℝ) : ℤ := ⌊(h-q)/a⌋

lemma mem_band_index {a : ℝ} (ha : 0<a) (q h : ℝ) : h ∈ band a q (index a q h) := by
  have hl := Int.floor_le ((h-q)/a)
  have hu := Int.lt_floor_add_one ((h-q)/a)
  have hl' := (le_div_iff₀ ha).mp hl
  have hu' := (div_lt_iff₀ ha).mp hu
  change q+↑⌊(h-q)/a⌋*a≤h ∧ h≤q+(↑⌊(h-q)/a⌋+1)*a
  exact ⟨by linarith,by linarith⟩

lemma lower_le_upper {a : ℝ} (ha : 0≤a) (q : ℝ) (k : ℤ) :
    q+(k:ℝ)*a ≤ q+((k:ℝ)+1)*a := by nlinarith

lemma overlap {a : ℝ} (ha : 0<a) {q h : ℝ} {j k : ℤ} (hjk : j<k)
    (hj : h ∈ band a q j) (hk : h ∈ band a q k) :
    h=q+((j:ℝ)+1)*a ∧ h=q+(k:ℝ)*a := by
  have hcast : (j:ℝ)+1≤k := by exact_mod_cast hjk
  have hm := mul_le_mul_of_nonneg_right hcast ha.le
  dsimp [band] at hj hk
  constructor <;> linarith [hj.2,hk.1]

/-- The finite list is precisely the closed bands meeting the prescribed
closed height window, not a truncation at individual points of a band. -/
noncomputable def processed (a q L U : ℝ) : Finset ℤ :=
  (Finset.Icc (index a q L-1) (index a q U)).filter
    (fun k => (band a q k ∩ Set.Icc L U).Nonempty)

lemma mem_processed {a : ℝ} (ha : 0<a) (q L U : ℝ) (k : ℤ) :
    k ∈ processed a q L U ↔ (band a q k ∩ Set.Icc L U).Nonempty := by
  rw [processed,Finset.mem_filter]
  constructor
  · exact And.right
  · intro he
    refine ⟨?_,he⟩
    obtain ⟨h,hb,hL,hU⟩ := he
    dsimp [band] at hb
    rw [Finset.mem_Icc]
    constructor
    · have htt : (L-q)/a ≤ (k:ℝ)+1 := (div_le_iff₀ ha).mpr (by linarith [hb.2])
      have hf : index a q L ≤ k+1 := by
        simpa only [index,Int.floor_intCast_add,Int.floor_intCast,Int.floor_one] using
          Int.floor_le_floor htt
      omega
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ ha).mpr
      linarith [hb.1]

lemma processed_covers {a : ℝ} (ha : 0<a) {q L U h : ℝ} (hh : h ∈ Set.Icc L U) :
    ∃ k ∈ processed a q L U, h ∈ band a q k := by
  exact ⟨index a q h,(mem_processed ha q L U _).mpr
    ⟨h,mem_band_index ha q h,hh⟩,mem_band_index ha q h⟩

/-- Small-ball height loss is proximity to a genuine band boundary. -/
def NearBoundary (a q h t : ℝ) : Prop := ∃ k : ℤ, |h-(q+k*a)|≤t

lemma same_band_of_avoid {a q h t x : ℝ} (ha : 0<a) (_ht : 0≤t)
    (hn : ¬NearBoundary a q h t) (hx : |x-h|≤t) :
    x ∈ band a q (index a q h) := by
  have hm := mem_band_index ha q h
  let k := index a q h
  have hlo : q+(k:ℝ)*a+t<h := by
    by_contra he
    have hb : |h-(q+k*a)|≤t := by rw [abs_of_nonneg (by linarith [hm.1])]; linarith
    exact hn ⟨k,hb⟩
  have hup : h+t<q+((k:ℝ)+1)*a := by
    by_contra he
    have hb : |h-(q+((k:ℝ)+1)*a)|≤t := by rw [abs_of_nonpos (by linarith [hm.2])]; linarith
    exact hn ⟨k+1,by simpa only [Int.cast_add,Int.cast_one] using hb⟩
  have hh := abs_le.mp hx
  exact ⟨by linarith,by linarith⟩

end Tiling
end PlanarL1

namespace PlanarL1.FiniteRandom
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma integer_interval_count (s : Finset ℤ) {step t : ℝ} (hs : 0<step)
    (ht : 0≤t) (c : ℝ) (hbound : ∀ i ∈ s, |c-step*i|≤t) :
    ((s.card:ℝ)-1)*step ≤ 2*t := by
  classical
  by_cases hn : s.Nonempty
  · let a := s.min' hn
    let b := s.max' hn
    have ha : a ∈ s := s.min'_mem hn
    have hb : b ∈ s := s.max'_mem hn
    have hab : a≤b := s.min'_le b hb
    have hc := Finset.card_le_card (show s ⊆ Finset.Icc a b from
      fun i hi => Finset.mem_Icc.mpr ⟨s.min'_le i hi,s.le_max' i hi⟩)
    have hd : (s.card:ℝ) ≤ (b:ℝ)-a+1 := by
      rw [Int.card_Icc] at hc
      have he : 0≤b+1-a := by omega
      have he' : ((b+1-a).toNat:ℤ)=b+1-a := Int.toNat_of_nonneg he
      have hh : (s.card:ℤ)≤b+1-a := by omega
      have hh' : (s.card:ℝ)≤(b:ℝ)+1-a := by exact_mod_cast hh
      linarith
    have hx := abs_le.mp (hbound a ha)
    have hy := abs_le.mp (hbound b hb)
    have hh := mul_le_mul_of_nonneg_right hd hs.le
    nlinarith
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero,zero_sub,neg_mul,one_mul]
    linarith

/-- Uniformly shifting a periodic tiling has its true one-dimensional bound.
The extra two grid points cover both endpoints, independently of the band index. -/
lemma periodic_probability (m : ℕ) (hm : 0 < m) {a t : ℝ} (ha : 0<a)
    (ht : 0≤t) (h : ℝ) :
    prob (fun i : Fin (m+1) => Tiling.NearBoundary a (a/m*i.val) h t) ≤
      (2*t+2*a/m)/a := by
  classical
  let A := event (fun i : Fin (m+1) => Tiling.NearBoundary a (a/m*i.val) h t)
  let B := A.erase (Fin.last m)
  have hmR : (0:ℝ)< m := by exact_mod_cast hm
  have hmI : (0:ℤ)< m := by exact_mod_cast hm
  have hb (i : B) : Tiling.NearBoundary a (a/m*i.val.val) h t :=
    (mem_event _ i.val).mp (Finset.mem_of_mem_erase i.property)
  choose k hk using hb
  let f (i : B) : ℤ := (m:ℤ)*k i+i.val.val
  have hlt (i : B) : (i.val.val:ℤ)< m := by
    have hn : i.val ≠ Fin.last m := (Finset.mem_erase.mp i.property).1
    have hv : i.val.val≠m := fun he => hn (Fin.ext he)
    exact_mod_cast (show i.val.val< m by omega)
  have hf : Function.Injective f := by
    intro i j he
    have hi := congrArg (fun z : ℤ => z % (m:ℤ)) he
    have hei (u : B) : f u % (m:ℤ) = u.val.val := by
      dsimp [f]
      rw [Int.add_emod,Int.mul_emod]
      simp only [Int.emod_self,zero_mul,Int.zero_emod,zero_add]
      rw [Int.emod_eq_of_lt (by positivity) (hlt u)]
      exact Int.emod_eq_of_lt (by positivity) (hlt u)
    rw [hei i,hei j] at hi
    exact Subtype.ext (Fin.ext (by exact_mod_cast hi))
  let S := B.attach.image f
  have hcard : S.card=B.card := by rw [Finset.card_image_of_injective _ hf,Finset.card_attach]
  have hcount := integer_interval_count S (div_pos ha hmR) ht h (by
    rintro z hz
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
    have eqn : a/m*(f i:ℝ)=a/m*i.val.val+(k i:ℝ)*a := by
      dsimp [f]
      push_cast
      field_simp
      ring
    rw [eqn]
    exact hk i)
  have hAB : A.card≤B.card+1 :=
    (Finset.card_le_card (show A ⊆ insert (Fin.last m) B from by
      intro i hi
      by_cases he : i=Fin.last m
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨he,hi⟩)))).trans
        (Finset.card_insert_le _ _)
  have hAB' : (A.card:ℝ)≤B.card+1 := by exact_mod_cast hAB
  rw [hcard] at hcount
  have hs : 0<a/m := div_pos ha hmR
  have hfinal : (A.card:ℝ)*(a/m)≤2*t+2*(a/m) := by nlinarith
  have hcoef : a/m*(m:ℝ)=a := div_mul_cancel₀ a (ne_of_gt hmR)
  have hfinal' := mul_le_mul_of_nonneg_right hfinal hmR.le
  rw [mul_assoc,hcoef] at hfinal'
  have hnonneg : 0≤(2*t+2*a/m)/a := by positivity
  change (A.card:ℝ)/(Fintype.card (Fin (m+1)):ℝ) ≤ _
  rw [Fintype.card_fin]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(m+1:ℕ))).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  push_cast
  have he : 2*t+2*(a/(m:ℝ))=2*t+2*a/m := by ring
  rw [he] at hfinal'
  exact hfinal'.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end PlanarL1.FiniteRandom

end


section

namespace PlanarL1.Tiling

/-- Strict padding in the actual floor-indexed band. -/
def Padded (a q h t : ℝ) : Prop :=
  q+(index a q h:ℝ)*a+t<h ∧ h<q+((index a q h:ℝ)+1)*a-t

lemma NearBoundary.mono {a q h s t : ℝ} (hm : s≤t) :
    NearBoundary a q h s → NearBoundary a q h t := fun ⟨k,hk⟩ => ⟨k,hk.trans hm⟩

lemma NearBoundary.perturb {a q h x t : ℝ} (hn : NearBoundary a q x t) :
    NearBoundary a q h (t+|x-h|) := by
  obtain ⟨k,hk⟩ := hn
  refine ⟨k,?_⟩
  have ht := abs_sub_le h x (q+k*a)
  rw [abs_sub_comm h x] at ht
  linarith

lemma padded_of_avoid {a q h t : ℝ} (ha : 0<a) (hn : ¬NearBoundary a q h t) :
    Padded a q h t := by
  have hm := mem_band_index ha q h
  constructor
  · by_contra he
    apply hn
    refine ⟨index a q h,?_⟩
    rw [abs_of_nonneg (by linarith [hm.1])]
    linarith
  · by_contra he
    apply hn
    refine ⟨index a q h+1,?_⟩
    rw [Int.cast_add,Int.cast_one,abs_of_nonpos (by linarith [hm.2])]
    linarith

lemma index_eq_of_mem_lt {a q h : ℝ} (ha : 0<a) (k : ℤ)
    (hl : q+(k:ℝ)*a≤h) (hu : h<q+((k:ℝ)+1)*a) : index a q h=k := by
  apply Int.floor_eq_iff.mpr
  exact ⟨(le_div_iff₀ ha).mpr (by linarith),(div_lt_iff₀ ha).mpr (by linarith)⟩

lemma same_index_of_avoid {a q h t x : ℝ} (ha : 0<a)
    (hn : ¬NearBoundary a q h t) (hx : |x-h|≤t) : index a q x=index a q h := by
  have hh := padded_of_avoid ha hn
  have hle := abs_le.mp hx
  exact index_eq_of_mem_lt ha _ (by linarith [hh.1]) (by linarith [hh.2])

lemma padded_pair {a q h x t e : ℝ} (ha : 0<a) (he : |x-h|≤e)
    (hn : ¬NearBoundary a q h (t+e)) : Padded a q h t ∧ Padded a q x t := by
  have he0 : 0≤e := (abs_nonneg _).trans he
  exact ⟨padded_of_avoid ha (fun hh => hn (hh.mono (by linarith))),
    padded_of_avoid ha (fun hh => hn (hh.perturb.mono (by linarith)))⟩

lemma band_subset_of_padding {a b q p h t : ℝ} (_ha : 0<a) (hb : 0<b)
    (hp : Padded a q h t) (hbt : b≤t) :
    band b p (index b p h) ⊆ band a q (index a q h) := by
  have hh := mem_band_index hb p h
  intro x hx
  change q+(index a q h:ℝ)*a≤x ∧ x≤q+((index a q h:ℝ)+1)*a
  change p+(index b p h:ℝ)*b≤x ∧ x≤p+((index b p h:ℝ)+1)*b at hx
  change p+(index b p h:ℝ)*b≤h ∧ h≤p+((index b p h:ℝ)+1)*b at hh
  exact ⟨by linarith [hp.1,hh.2,hx.1],by linarith [hp.2,hh.1,hx.2]⟩

end PlanarL1.Tiling

namespace PlanarL1.FiniteRandom

lemma prob_or_le {Ω : Type*} [Fintype Ω] (P Q : Ω → Prop) :
    prob (fun ω => P ω ∨ Q ω)≤prob P+prob Q := by
  classical
  have h := prob_union_bound (Finset.univ : Finset Bool) (fun b => if b then P else Q)
  simpa only [Finset.mem_univ,true_and,Bool.exists_bool,Bool.false_eq_true,ite_false,ite_true,
    Fintype.sum_bool,or_comm] using h

lemma prob_compl {Ω : Type*} [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) :
    prob (fun ω => ¬P ω)=1-prob P := by
  rw [←Execution.prob_uniform,←Execution.prob_uniform]
  exact Execution.prob_compl _ _

lemma prob_eval_bound {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]
    (i : I) (P : Ω → Prop) {b : ℝ} (h : prob P≤b) :
    prob (fun ω : I → Ω => P (ω i))≤b := by
  classical
  apply prob_update_bound i
  intro α
  simpa only [Function.update_self] using h

end PlanarL1.FiniteRandom

namespace PlanarL1.Tiling
open Parameters FiniteRandom

/-- The two endpoint height tests use one shift, so their failures are bounded
by an enlarged interval, not by a union bound over the vertices or columns. -/
lemma height_pair_probability (m : ℕ) (hm : 10000 ≤ m) {a h x : ℝ} (ha : 0<a)
    (htrim : a₂≤a) (hd : |x-h|≤a₂/10000) :
    prob (fun i : Fin (m+1) => ¬(Padded a (a/m*i.val) h (a/10) ∧
      Padded a (a/m*i.val) x (a/10)))≤21/100 := by
  classical
  have hm0 : 0 < m := by omega
  have hbad : prob (fun i : Fin (m+1) => ¬(Padded a (a/m*i.val) h (a/10) ∧
      Padded a (a/m*i.val) x (a/10))) ≤
      prob (fun i : Fin (m+1) => NearBoundary a (a/m*i.val) h (a/10+a₂/10000)) := by
    apply prob_mono
    intro i hi
    by_contra hh
    exact hi (padded_pair ha hd hh)
  have hp := periodic_probability m hm0 ha (show 0≤a/10+a₂/10000 by have hb := interpolationB.2.1; positivity) h
  apply hbad.trans (hp.trans _)
  have hmR : (10000:ℝ) ≤ m := by exact_mod_cast hm
  have hmesh : a/m≤a/10000 := div_le_div_of_nonneg_left ha.le (by norm_num) hmR
  apply (div_le_iff₀ ha).mpr
  rw [mul_div_assoc]
  linarith

lemma narrow_contained {q p h : ℝ} (hp : Padded a₁ q h (a₁/10)) :
    band a₂ p (index a₂ p h) ⊆ band a₁ q (index a₁ q h) :=
  band_subset_of_padding interpolationA.2.1 interpolationB.2.1 hp (by norm_num [a₁,a₂])

end PlanarL1.Tiling

end


section

namespace PlanarL1.Tiling
lemma unique_band_of_padded {a q h t : ℝ} (ha : 0<a) (ht : 0≤t)
    (hp : Padded a q h t) {n : ℤ} (hn : h ∈ band a q n) : n=index a q h := by
  rcases lt_trichotomy n (index a q h) with hl | he | hu
  · have hnl : (n:ℝ)+1≤(index a q h:ℝ) := by exact_mod_cast (show n+1 ≤ index a q h by omega)
    have hb := mul_le_mul_of_nonneg_right hnl ha.le
    have hx := hn.2
    change h≤q+((n:ℝ)+1)*a at hx
    have hh := hp.1
    change q+(index a q h:ℝ)*a+t<h at hh
    linarith
  · exact he
  · have hnl : (index a q h:ℝ)+1≤(n:ℝ) := by exact_mod_cast (show index a q h+1≤n by omega)
    have hb := mul_le_mul_of_nonneg_right hnl ha.le
    have hx := hn.1
    change q+(n:ℝ)*a≤h at hx
    have hh := hp.2
    change h<q+((index a q h:ℝ)+1)*a-t at hh
    linarith
end PlanarL1.Tiling

end

end OAI
