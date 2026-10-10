import OAI.Combinatorics.HadwigerCounterexample.OrientationRankBounds

namespace OAI

/-! # Basis Conditioning -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Finset Filter Function
open scoped BigOperators
variable {p : Shape} {n N : ℕ} {I : Type} [Fintype I] [DecidableEq I]

theorem totalRank_pos {x : Profile p n} (h : x≠0) :
    0<totalRank x := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp h
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun i _=>Nat.zero_le ((x i).rank))
    (Finset.mem_univ i))
  apply Nat.pos_of_ne_zero; intro h
  obtain ⟨A,B,hh⟩ := mul_factor (x i) 0 h.le
  apply hi; ext a b; rw [←hh,Matrix.mul_apply]; simp

def glintRate (K : ℕ) := bp (-((K^2:ℕ):ℝ)-3)

theorem glint_within {K d : ℕ} (h : d≤ K^2) :
    glintRate K ≤ (1/8:ℝ)*bp (- (d:ℝ)) := by
  unfold glintRate
  have hh : bp (-3)=1/8 := by norm_num [bp]
  rw [←hh,←bp_add]
  exact bp_le (by linarith only [(show (d:ℝ) ≤ ((K^2:ℕ):ℝ) from by exact_mod_cast h)])

namespace Template
variable (v : Solo p)

def stains (m : Mixer p n) (f : Vec I →ₗ[F] Profile p n) (z : Knobs p.g n) : Vec I :=
  fun i=> Tsym m (f (Pi.single i 1)) (useAtom p (v.t ()) (v.s ()) (v.f ()) z)
theorem staining (m : Mixer p n) (f : Vec I→ₗ[F] Profile p n) (z : Knobs p.g n) (i : Vec I) :
    vectorPhase i (stains v m f z)=shanty v m (f i) z := by
  classical
  let h := LinearMap.flip (Tsym m) (useAtom p (v.t ()) (v.s ()) (v.f ()) z) ∘ₗ f
  have ht : h i=h (∑ j: I,i j • (Pi.single j 1 : Vec I)) := by
    have he (j:I) : i j • (Pi.single j 1 : Vec I)=Pi.single j (i j) := by
      funext k; by_cases hh:k=j <;> simp [hh]
    simp_rw [he]
    rw [Finset.univ_sum_single]
  change wsign (∑ j:I,i j*h (Pi.single j 1))=wsign (h i)
  rw [ht,map_sum]; simp_rw [map_smul]; rfl

def luminous (v : Solo p) (m : Mixer p n) (w : Wgt (Knobs p.g n)) (D : AtomKey (p:=p) (v.t ())
    N →Prop) (K : ℕ) (i : Orient p n N) :=
  let P := offBeat v D i
  0<pr w P ∧ ∀ (d : ℕ), d≤ K^2 → ∀ f : Vec (Fin d)→ₗ[F] Profile p n,
    Injective f → (∀ x,totalRank (f x)≤K) → ∀ x,
    (7/8:ℝ)*bp (-(d:ℝ)) ≤ pr (onW w P) (fun z=> stains v m f z=x)

set_option maxHeartbeats 800000 in
theorem glow_luminous (v : Solo p) (m : Mixer p n) (w : Wgt (Knobs p.g n))
    (hw : IsLaw w)
    (S : AtomKey (p:=p) (v.t ()) N → Prop)
    (K : ℕ) (i : Orient p n N) (δ : ℝ) (hδ : 0<δ) (he : δ ≤ pr w (offBeat v S i))
    (h : ∀ x, 0<totalRank x → totalRank x≤K → ¬ glow v m w S (glintRate K) δ x i) :
    luminous v m w S K i := by
  classical
  let P := offBeat v S i
  have hP : 0<pr w P := hδ.trans_le he
  let u := onW w P; have hu : IsLaw u := on_law hw.nz hP
  refine ⟨hP,fun d hd f hf hg x => ?_⟩
  let s := stains v m f
  have heq :
      pr u (fun z => s z=x) = avg unif (fun i => vectorPhase i x*
          avg u (fun z => vectorPhase i (s z))) := by
    unfold pr
    simp_rw [vector_expand]
    rw [avg_avg]
    apply avg_congr
    intro i hi
    rw [avg_mul]; ring
  let b := bp (-(d:ℝ))
  let Q (k : Vec (Fin d)) := vectorPhase k x * avg u (fun z => vectorPhase k (s z))
  have hb : 0 < b := bp_pos _
  have hh k : ind (k=0)-b/8 ≤ Q k := by
    by_cases hk : k=0
    · subst k
      have hQ : Q 0=1 := by unfold Q; simp only [vectorPhase,zero_dotProduct,wsign_zero,one_mul,
        hu.avg_const]
      rw [ind_one (show (0:Vec (Fin d))=0 from rfl),hQ]; linarith
    let k' := f k
    have hT := h k' (totalRank_pos (hf.ne hk |>.trans_eq (map_zero f))) (hg k)
    have hz : |zsumPeak p w (v.shanty m k') P| ≤ (glintRate K)*pr w P :=
      le_of_lt (lt_of_not_ge (fun h => hT ⟨he,h⟩))
    have ht :
        avg u (fun z => vectorPhase k (s z))=
          zsumPeak p w (v.shanty m k') P/pr w P := by
      unfold s u onW; simp_rw [staining]; rw [avg_norm,subW_tot]
      congr 1; simp [zsumPeak,avg,subW,mul_assoc,k']
    have h1 : |Q k|≤b/8 := by
      unfold Q; rw [ht,abs_mul,vectorPhase,wsign_abs,one_mul,abs_div,abs_of_pos hP]
      refine le_trans ((div_le_iff₀ hP).mpr hz) ((glint_within hd).trans_eq (by unfold b; ring))
    rw [ind_zero hk,zero_sub]; exact (abs_le.mp h1).1
  have h0 : unif (0:Vec (Fin d))=b := by
    unfold b; rw [unif_apply,card_space,dim_vec,bp_neg,Fintype.card_fin]
  change _ ≤ pr u (fun z => s z=x)
  rw [heq]
  refine le_trans ?_ (avg_mono unif_law.nz hh)
  rw [avg_sub,unif_law.avg_const,
    show avg unif (fun i : Vec (Fin d)=> ind (i=0))=b from (pr_point' unif _).trans h0]
  change 7/8*b≤_
  linarith
end Template
end HadwigerCounterexample

end

end OAI
