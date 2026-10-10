import Mathlib
import OAI.Computability.VertexCover.Machines.ExpanderCorrect

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                  
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

theorem listBits_length_bound {α : Type} (e : α → List Bool) (xs : List α) (B : ℕ)
    (h : ∀ x ∈ xs, (e x).length ≤ B) :
    (listBits e xs).length ≤ xs.length*(2*B+2)+1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.length_cons,listBits_cons_length]
    nlinarith

namespace ExpandMachine

noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits Sigma.fst :=
  (Poly.fst natBits (listBits natBits)).encodeCongr erase (fun _ => rfl) (fun _ => rfl)

 theorem code_bound {q : ℕ} (T : Input q) :
    (code T).length ≤ 2*T.1+2+(T.1*q)*(2*(T.1*q)+2) := by
  have hb := listBits_length_bound natBits (T.2.rows.toList.map Fin.val) (T.1*q) (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    simpa only [natBits_length] using Nat.le_of_lt i.isLt)
  simp only [List.length_map,Vector.length_toList] at hb
  simp only [code,dataCode,erase,prodBits,pairBits_length,natBits_length]
  omega

 theorem vertices_le_code {q : ℕ} (T : Input q) : T.1 ≤ (code T).length := by
  simp only [code,dataCode,erase,prodBits,pairBits_length,natBits_length]
  omega

def capped {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d)
    (p : ℕ × Input (d*d)) : ℕ × Input (d*d) :=
  (p.1,if p.1 ≤ p.2.1 then p.2 else step H p.2)

noncomputable def cappedPoly {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) :
    Poly (prodBits natBits (code (q := d*d))) (prodBits natBits code) (capped H) := by
  let ck := Poly.fst natBits (code (q := d*d))
  let ct := Poly.snd natBits (code (q := d*d))
  let test := (ck.pair (ct.comp verticesPoly)).comp Poly.natLE
  exact ck.pair ((test.ite ct (ct.comp (stepPoly H))).congr (fun p => by simp))

 theorem capped_vertex_bound {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d)
    (p : ℕ × Input (d*d)) : (capped H p).2.1 ≤ p.2.1+((d*d)*(d*d))*p.1 := by
  dsimp only [capped]
  split
  · omega
  · rename_i h
    have hm := Nat.mul_le_mul_right ((d*d)*(d*d)) (Nat.le_of_lt (Nat.lt_of_not_ge h))
    dsimp only [step]
    nlinarith

 theorem capped_iterate_bound {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d)
    (n : ℕ) (p : ℕ × Input (d*d)) :
    (Iterate.run (capped H) n p).1=p.1 ∧
    (Iterate.run (capped H) n p).2.1 ≤ max p.2.1 (((d*d)*(d*d))*p.1) := by
  induction n generalizing p with
  | zero => exact ⟨rfl,Nat.le_max_left _ _⟩
  | succ n ih =>
    have hh := ih (capped H p)
    refine ⟨hh.1,hh.2.trans ?_⟩
    apply max_le
    · simp only [capped]
      split
      · exact Nat.le_max_left _ _
      · rename_i h
        change p.2.1*((d*d)*(d*d)) ≤ _
        rw [Nat.mul_comm]
        exact (Nat.mul_le_mul_left _ (Nat.le_of_lt (Nat.lt_of_not_ge h))).trans (Nat.le_max_right _ _)
    · exact Nat.le_max_right _ _

theorem encoding_bound (q g n p v₀ v l N L : ℕ)
    (hn : n ≤ N) (hp : p ≤ N) (hv : v₀ ≤ N) (hl : l ≤ n)
    (hb : v ≤ max v₀ (g*p)) (hlen : L ≤ 2*v+2+(v*q)*(2*(v*q)+2)) :
    2*l+1+(2*p+1+L) ≤ 20*((g+1)*(q+1)+1)^2*(N+1)^2 := by
  let C := g+1
  let R := C*(q+1)+1
  let B := R*(N+1)
  have hm : v ≤ C*N := by
    apply hb.trans
    apply max_le
    · dsimp [C]; nlinarith only [hv,Nat.zero_le (g*N)]
    · exact (Nat.mul_le_mul_left g hp).trans (by dsimp [C]; nlinarith only [Nat.zero_le N])
  have hr : 1 ≤ R := by dsimp [R]; omega
  have hc : C ≤ R := by dsimp [R]; nlinarith only [Nat.zero_le (C*q)]
  have hcq : C*q ≤ R := by dsimp [R]; nlinarith only [Nat.zero_le C]
  have hB : 1 ≤ B := Nat.mul_le_mul hr (Nat.succ_le_succ (Nat.zero_le N))
  have hNB : N ≤ B := (Nat.le_succ N).trans (by
    simpa only [one_mul] using Nat.mul_le_mul_right (N+1) hr)
  have hvB : v ≤ B := hm.trans (Nat.mul_le_mul hc (Nat.le_succ N))
  have hqB : v*q ≤ B := by
    calc
      v*q ≤ C*N*q := Nat.mul_le_mul_right q hm
      _ = (C*q)*N := by ring
      _ ≤ B := Nat.mul_le_mul hcq (Nat.le_succ N)
  have hsquare := Nat.mul_le_mul hqB hqB
  have hlinear : B ≤ B*B := by simpa only [one_mul] using Nat.mul_le_mul_right B hB
  have hlB := (hl.trans hn).trans hNB
  have hpB := hp.trans hNB
  change _ ≤ 20*R^2*(N+1)^2
  rw [show 20*R^2*(N+1)^2=20*B^2 by dsimp [B]; ring]
  nlinarith only [hB,hlinear,hvB,hqB,hsquare,hlen,hlB,hpB]

noncomputable def cappedIteratePoly {d : ℕ} (H : ExpanderTables.Table ((d*d)*(d*d)) d) :
    Poly (prodBits natBits (prodBits natBits (code (q := d*d))))
      (prodBits natBits code) (fun p => Iterate.run (capped H) p.1 p.2) := by
  let g := (d*d)*(d*d)
  let Q := d*d
  let size : Polynomial ℕ := Polynomial.C (20*((g+1)*(Q+1)+1)^2)*(Polynomial.X+1)^2
  apply Poly.iterate _ (cappedPoly H) size
  intro n p k l h
  let N := (prodBits natBits (prodBits natBits (code (q := d*d))) (n,p)).length
  have hn : n ≤ N := by dsimp [N,prodBits]; simp only [pairBits_length,natBits_length]; omega
  have hp : p.1 ≤ N := by dsimp [N,prodBits]; simp only [pairBits_length,natBits_length]; omega
  have hv : p.2.1 ≤ N := by
    have hh := vertices_le_code p.2
    dsimp [N,prodBits]; simp only [pairBits_length,natBits_length]; omega
  have hb := capped_iterate_bound H k p
  change (prodBits natBits (prodBits natBits (code (q := d*d)))
    (l,Iterate.run (capped H) k p)).length ≤ size.eval N
  simp only [prodBits,pairBits_length,natBits_length,hb.1,size,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  exact encoding_bound Q g n p.1 p.2.1 _ l N _ hn hp hv (by omega) hb.2 (code_bound _)

end ExpandMachine
end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
